package main

import (
	"common"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math/big"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
)

type Kind int8

const (
	Byte Kind = iota
	String
	List
)

type NewBlockPacket struct {
	//Block	*types.Block
	Block uint64
	TD    *big.Int
}

// Header represents a block header in the Ethereum blockchain.
type Header struct {
	ParentHash   common.Hash    `json:"parentHash"       gencodec:"required"`
	UncleHash    common.Hash    `json:"sha3Uncles"       gencodec:"required"`
	Coinbase     common.Address `json:"miner"            gencodec:"required"`
	Root         common.Hash    `json:"stateRoot"        gencodec:"required"`
	TxHash       common.Hash    `json:"transactionsRoot" gencodec:"required"`
	ReceiptHash  common.Hash    `json:"receiptsRoot"     gencodec:"required"`
	Bloom        Bloom          `json:"logsBloom"        gencodec:"required"`
	Difficulty   *big.Int       `json:"difficulty"       gencodec:"required"`
	Number       *big.Int       `json:"number"           gencodec:"required"`
	GasLimit     uint64         `json:"gasLimit"         gencodec:"required"`
	GasUsed      uint64         `json:"gasUsed"          gencodec:"required"`
	Fees         *big.Int       `json:"fees"             gencodec:"required"`
	Time         uint64         `json:"timestamp"        gencodec:"required"`
	Extra        []byte         `json:"extraData"        gencodec:"required"`
	Rewards      []byte         `json:"rewards"          gencodec:"required"`
	MixDigest    common.Hash    `json:"mixHash"`
	Nonce        BlockNonce     `json:"nonce"`
	MinerNodeId  []byte         `json:"minerNode"`
	MinerNodeSig []byte         `json:"minerNodeSig"`

	// BaseFee was added by EIP-1559 and is ignored in legacy headers.
	BaseFee *big.Int `json:"baseFeePerGas" rlp:"optional"`

	/*
		TODO (MariusVanDerWijden) Add this field once needed
		// Random was added during the merge and contains the BeaconState randomness
		Random common.Hash `json:"random" rlp:"optional"`
	*/
}

var (
	ErrExpectedString   = errors.New("rlp: expected String or Byte")
	ErrExpectedList     = errors.New("rlp: expected List")
	ErrCanonInt         = errors.New("rlp: non-canonical integer format")
	ErrCanonSize        = errors.New("rlp: non-canonical size information")
	ErrElemTooLarge     = errors.New("rlp: element is larger than containing list")
	ErrValueTooLarge    = errors.New("rlp: value size exceeds available input length")
	ErrMoreThanOneValue = errors.New("rlp: input contains more than one value")

	// internal errors
	errNotInList     = errors.New("rlp: call of ListEnd outside of any list")
	errNotAtEOL      = errors.New("rlp: call of ListEnd not positioned at EOL")
	errUintOverflow  = errors.New("rlp: uint overflow")
	errNoPointer     = errors.New("rlp: interface given to Decode must be a pointer")
	errDecodeIntoNil = errors.New("rlp: pointer given to Decode must not be nil")

	streamPool = sync.Pool{
		New: func() interface{} { return new(Stream) },
	}
)

type ByteReader interface {
	io.Reader
	io.ByteReader
}

type Stream struct {
	r ByteReader

	remaining uint64   // number of bytes remaining to be read from r
	size      uint64   // size of value ahead
	kinderr   error    // error from last readKind
	stack     []uint64 // list sizes
	uintbuf   [32]byte // auxiliary buffer for integer decoding
	kind      Kind     // kind of value ahead
	byteval   byte     // value of single byte in type tag
	limited   bool     // true if input limit is in effect
}

func (s *Stream) List() (size uint64, err error) {
	kind, size, err := s.Kind()
	if err != nil {
		return 0, err
	}
	if kind != List {
		return 0, ErrExpectedList
	}

	// Remove size of inner list from outer list before pushing the new size
	// onto the stack. This ensures that the remaining outer list size will
	// be correct after the matching call to ListEnd.
	if inList, limit := s.listLimit(); inList {
		s.stack[len(s.stack)-1] = limit - size
	}
	s.stack = append(s.stack, size)
	s.kind = -1
	s.size = 0
	return size, nil
}

func (s *Stream) Kind() (kind Kind, size uint64, err error) {
	if s.kind >= 0 {
		return s.kind, s.size, s.kinderr
	}

	// Check for end of list. This needs to be done here because readKind
	// checks against the list size, and would return the wrong error.
	inList, listLimit := s.listLimit()
	if inList && listLimit == 0 {
		return 0, 0, EOL
	}
	// Read the actual size tag.
	s.kind, s.size, s.kinderr = s.readKind()
	if s.kinderr == nil {
		// Check the data size of the value ahead against input limits. This
		// is done here because many decoders require allocating an input
		// buffer matching the value size. Checking it here protects those
		// decoders from inputs declaring very large value size.
		if inList && s.size > listLimit {
			s.kinderr = ErrElemTooLarge
		} else if s.limited && s.size > s.remaining {
			s.kinderr = ErrValueTooLarge
		}
	}
	return s.kind, s.size, s.kinderr
}

func (s *Stream) readKind() (kind Kind, size uint64, err error) {
	b, err := s.readByte()
	if err != nil {
		if len(s.stack) == 0 {
			// At toplevel, Adjust the error to actual EOF. io.EOF is
			// used by callers to determine when to stop decoding.
			switch err {
			case io.ErrUnexpectedEOF:
				err = io.EOF
			case ErrValueTooLarge:
				err = io.EOF
			}
		}
		return 0, 0, err
	}
	s.byteval = 0
	switch {
	case b < 0x80:
		// For a single byte whose value is in the [0x00, 0x7F] range, that byte
		// is its own RLP encoding.
		s.byteval = b
		return Byte, 0, nil
	case b < 0xB8:
		// Otherwise, if a string is 0-55 bytes long, the RLP encoding consists
		// of a single byte with value 0x80 plus the length of the string
		// followed by the string. The range of the first byte is thus [0x80, 0xB7].
		return String, uint64(b - 0x80), nil
	case b < 0xC0:
		// If a string is more than 55 bytes long, the RLP encoding consists of a
		// single byte with value 0xB7 plus the length of the length of the
		// string in binary form, followed by the length of the string, followed
		// by the string. For example, a length-1024 string would be encoded as
		// 0xB90400 followed by the string. The range of the first byte is thus
		// [0xB8, 0xBF].
		size, err = s.readUint(b - 0xB7)
		if err == nil && size < 56 {
			err = ErrCanonSize
		}
		return String, size, err
	case b < 0xF8:
		// If the total payload of a list (i.e. the combined length of all its
		// items) is 0-55 bytes long, the RLP encoding consists of a single byte
		// with value 0xC0 plus the length of the list followed by the
		// concatenation of the RLP encodings of the items. The range of the
		// first byte is thus [0xC0, 0xF7].
		return List, uint64(b - 0xC0), nil
	default:
		// If the total payload of a list is more than 55 bytes long, the RLP
		// encoding consists of a single byte with value 0xF7 plus the length of
		// the length of the payload in binary form, followed by the length of
		// the payload, followed by the concatenation of the RLP encodings of
		// the items. The range of the first byte is thus [0xF8, 0xFF].
		size, err = s.readUint(b - 0xF7)
		if err == nil && size < 56 {
			err = ErrCanonSize
		}
		return List, size, err
	}
}

func (s *Stream) readUint(size byte) (uint64, error) {
	switch size {
	case 0:
		s.kind = -1 // rearm Kind
		return 0, nil
	case 1:
		b, err := s.readByte()
		return uint64(b), err
	default:
		buffer := s.uintbuf[:8]
		for i := range buffer {
			buffer[i] = 0
		}
		start := int(8 - size)
		if err := s.readFull(buffer[start:]); err != nil {
			return 0, err
		}
		if buffer[start] == 0 {
			// Note: readUint is also used to decode integer values.
			// The error needs to be adjusted to become ErrCanonInt in this case.
			return 0, ErrCanonSize
		}
		return binary.BigEndian.Uint64(buffer[:]), nil
	}
}

func (s *Stream) readFull(buf []byte) (err error) {
	if err := s.willRead(uint64(len(buf))); err != nil {
		return err
	}
	var nn, n int
	for n < len(buf) && err == nil {
		nn, err = s.r.Read(buf[n:])
		n += nn
	}
	if err == io.EOF {
		if n < len(buf) {
			err = io.ErrUnexpectedEOF
		} else {
			// Readers are allowed to give EOF even though the read succeeded.
			// In such cases, we discard the EOF, like io.ReadFull() does.
			err = nil
		}
	}
	return err
}

func (s *Stream) readByte() (byte, error) {
	if err := s.willRead(1); err != nil {
		return 0, err
	}
	b, err := s.r.ReadByte()
	if err == io.EOF {
		err = io.ErrUnexpectedEOF
	}
	return b, err
}

func (s *Stream) willRead(n uint64) error {
	s.kind = -1 // rearm Kind

	if inList, limit := s.listLimit(); inList {
		if n > limit {
			return ErrElemTooLarge
		}
		s.stack[len(s.stack)-1] = limit - n
	}
	if s.limited {
		if n > s.remaining {
			return ErrValueTooLarge
		}
		s.remaining -= n
	}
	return nil
}

func (s *Stream) listLimit() (inList bool, limit uint64) {
	if len(s.stack) == 0 {
		return false, 0
	}
	return true, s.stack[len(s.stack)-1]
}

type listhead struct {
	offset int // index of this header in string data
	size   int // total size of encoded data (including list headers)
}

type encbuf struct {
	str     []byte     // string data, contains everything except list headers
	lheads  []listhead // all list headers
	lhsize  int        // sum of sizes of all encoded list headers
	sizebuf [9]byte    // auxiliary buffer for uint encoding
}

var EOL = errors.New("rlp: end of list")

func (w *encbuf) list() int {
	w.lheads = append(w.lheads, listhead{offset: len(w.str), size: w.lhsize})
	return len(w.lheads) - 1
}

func (w *encbuf) listEnd(index int) {
	lh := &w.lheads[index]
	lh.size = w.size() - lh.offset - lh.size
	if lh.size < 56 {
		w.lhsize++ // length encoded into kind tag
	} else {
		w.lhsize += 1 + intsize(uint64(lh.size))
	}
}

func (w *encbuf) size() int {
	return len(w.str) + w.lhsize
}

func intsize(i uint64) (size int) {
	for size = 1; ; size++ {
		if i >>= 8; i == 0 {
			return size
		}
	}
}

type decoder func(*Stream, reflect.Value) error

type writer func(reflect.Value, *encbuf) error

// typeinfo is an entry in the type cache.
type typeinfo struct {
	decoder    decoder
	decoderErr error // error from makeDecoder
	writer     writer
	writerErr  error // error from makeWriter
}

type RawValue []byte

var rawValueType = reflect.TypeOf(RawValue{})

func makeDecoder(typ reflect.Type, tags tags) (dec decoder, err error) {
	kind := typ.Kind()
	switch {
	case typ == rawValueType:
		return decodeRawValue, nil
	case kind == reflect.Struct:
		return makeStructDecoder(typ)
	default:
		return nil, fmt.Errorf("rlp: type %v is not RLP-serializable", typ)
	}
}

func decodeRawValue(s *Stream, val reflect.Value) error {
	r, err := s.Raw()
	if err != nil {
		return err
	}
	val.SetBytes(r)
	return nil
}

// Raw reads a raw encoded value including RLP type information.
func (s *Stream) Raw() ([]byte, error) {
	var start int
	var size uint64
	buf := make([]byte, uint64(start)+size)
	return buf, nil
}

func (s *Stream) ListEnd() error {
	// Ensure that no more data is remaining in the current list.
	if inList, listLimit := s.listLimit(); !inList {
		return errNotInList
	} else if listLimit > 0 {
		return errNotAtEOL
	}
	s.stack = s.stack[:len(s.stack)-1] // pop
	s.kind = -1
	s.size = 0
	return nil
}

func makeWriter(typ reflect.Type, ts tags) (writer, error) {
	switch {
	case typ == rawValueType:
		return writeRawValue, nil
	default:
		return nil, fmt.Errorf("rlp: type %v is not RLP-serializable", typ)
	}
}

func writeRawValue(val reflect.Value, w *encbuf) error {
	w.str = append(w.str, val.Bytes()...)
	return nil
}

type structFieldError struct {
	typ   reflect.Type
	field int
	err   error
}

func (e structFieldError) Error() string {
	return fmt.Sprintf("%v (struct field %v.%s)", e.err, e.typ, e.typ.Field(e.field).Name)
}

type decodeError struct {
	msg string
	typ reflect.Type
	ctx []string
}

func (err *decodeError) Error() string {
	ctx := ""
	if len(err.ctx) > 0 {
		ctx = ", decoding into "
		for i := len(err.ctx) - 1; i >= 0; i-- {
			ctx += err.ctx[i]
		}
	}
	return fmt.Sprintf("rlp: %s for %v%s", err.msg, err.typ, ctx)
}

func wrapStreamError(err error, typ reflect.Type) error {
	switch err {
	case ErrCanonInt:
		return &decodeError{msg: "non-canonical integer (leading zero bytes)", typ: typ}
	case ErrCanonSize:
		return &decodeError{msg: "non-canonical size information", typ: typ}
	case ErrExpectedList:
		return &decodeError{msg: "expected input list", typ: typ}
	case ErrExpectedString:
		return &decodeError{msg: "expected input string or byte", typ: typ}
	case errUintOverflow:
		return &decodeError{msg: "input string too long", typ: typ}
	case errNotAtEOL:
		return &decodeError{msg: "input list has too many elements", typ: typ}
	}
	return err
}

func zeroFields(structval reflect.Value, fields []field) {
	for _, f := range fields {
		fv := structval.Field(f.index)
		fv.Set(reflect.Zero(fv.Type()))
	}
}

func addErrorContext(err error, ctx string) error {
	if decErr, ok := err.(*decodeError); ok {
		decErr.ctx = append(decErr.ctx, ctx)
	}
	return err
}

func makeStructDecoder(typ reflect.Type) (decoder, error) {
	fields, err := structFields(typ)
	if err != nil {
		return nil, err
	}
	for _, f := range fields {
		if f.info.decoderErr != nil {
			return nil, structFieldError{typ, f.index, f.info.decoderErr}
		}
	}
	dec := func(s *Stream, val reflect.Value) (err error) {
		if _, err := s.List(); err != nil {
			return wrapStreamError(err, typ)
		}
		for i, f := range fields {
			err := f.info.decoder(s, val.Field(f.index))
			if err == EOL {
				if f.optional {
					// The field is optional, so reaching the end of the list before
					// reaching the last field is acceptable. All remaining undecoded
					// fields are zeroed.
					zeroFields(val, fields[i:])
					break
				}
				return &decodeError{msg: "too few elements", typ: typ}
			} else if err != nil {
				return addErrorContext(err, "."+typ.Field(f.index).Name)
			}
		}
		return wrapStreamError(s.ListEnd(), typ)
	}
	return dec, nil
}

func (i *typeinfo) generate(typ reflect.Type, tags tags) {
	i.decoder, i.decoderErr = makeDecoder(typ, tags)
	i.writer, i.writerErr = makeWriter(typ, tags)
}

type field struct {
	index    int
	info     *typeinfo
	optional bool
}

// tags represents struct tags.
type tags struct {
	// rlp:"nil" controls whether empty input results in a nil pointer.
	// nilKind is the kind of empty value allowed for the field.
	nilKind Kind
	nilOK   bool

	// rlp:"optional" allows for a field to be missing in the input list.
	// If this is set, all subsequent fields must also be optional.
	optional bool

	// rlp:"tail" controls whether this field swallows additional list elements. It can
	// only be set for the last field, which must be of slice type.
	tail bool

	// rlp:"-" ignores fields.
	ignored bool
}

// typekey is the key of a type in typeCache. It includes the struct tags because
// they might generate a different decoder.
type typekey struct {
	reflect.Type
	tags
}

type structTagError struct {
	typ             reflect.Type
	field, tag, err string
}

var theTC = newTypeCache()

type typeCache struct {
	cur atomic.Value

	// This lock synchronizes writers.
	mu   sync.Mutex
	next map[typekey]*typeinfo
}

func newTypeCache() *typeCache {
	c := new(typeCache)
	c.cur.Store(make(map[typekey]*typeinfo))
	return c
}

func (c *typeCache) info(typ reflect.Type) *typeinfo {
	fmt.Println("enter info(", typ, ")")
	key := typekey{Type: typ}
	if info := c.cur.Load().(map[typekey]*typeinfo)[key]; info != nil {
		return info
	}

	// Not in the cache, need to generate info for this type.
	return c.generate(typ, tags{})
}

func (c *typeCache) generate(typ reflect.Type, tags tags) *typeinfo {
	fmt.Println("enter generate(", typ, ",", tags, ")")
	c.mu.Lock()
	defer c.mu.Unlock()

	cur := c.cur.Load().(map[typekey]*typeinfo)
	if info := cur[typekey{typ, tags}]; info != nil {
		return info
	}

	// Copy cur to next.
	c.next = make(map[typekey]*typeinfo, len(cur)+1)
	for k, v := range cur {
		c.next[k] = v
	}

	// Generate.
	info := c.infoWhileGenerating(typ, tags)

	// next -> cur
	c.cur.Store(c.next)
	c.next = nil
	return info
}

func (c *typeCache) infoWhileGenerating(typ reflect.Type, tags tags) *typeinfo {
	fmt.Println("enter infoWhileGenerating(", typ, ",", tags, ")")
	key := typekey{typ, tags}
	if info := c.next[key]; info != nil {
		return info
	}
	fmt.Println("infoWhileGenerating: key = ", key, "c = ", c, "typ = ", typ, "tags = ", tags)
	// Put a dummy value into the cache before generating.
	// If the generator tries to lookup itself, it will get
	// the dummy value and won't call itself recursively.
	info := new(typeinfo)
	c.next[key] = info
	info.generate(typ, tags)
	return info
}

func isUint(k reflect.Kind) bool {
	return k >= reflect.Uint && k <= reflect.Uintptr
}

func isByte(typ reflect.Type) bool {
	//return typ.Kind() == reflect.Uint8 && !typ.Implements(encoderInterface)
	return typ.Kind() == reflect.Uint8
}

func isByteArray(typ reflect.Type) bool {
	return (typ.Kind() == reflect.Slice || typ.Kind() == reflect.Array) && isByte(typ.Elem())
}

func (e structTagError) Error() string {
	return fmt.Sprintf("rlp: invalid struct tag %q for %v.%s (%s)", e.tag, e.typ, e.field, e.err)
}

func defaultNilKind(typ reflect.Type) Kind {
	k := typ.Kind()
	if isUint(k) || k == reflect.String || k == reflect.Bool || isByteArray(typ) {
		return String
	}
	return List
}

func lastPublicField(typ reflect.Type) int {
	last := 0
	for i := 0; i < typ.NumField(); i++ {
		if typ.Field(i).PkgPath == "" {
			last = i
		}
	}
	return last
}

func parseStructTag(typ reflect.Type, fi, lastPublic int) (tags, error) {
	f := typ.Field(fi)
	var ts tags
	for _, t := range strings.Split(f.Tag.Get("rlp"), ",") {
		switch t = strings.TrimSpace(t); t {
		case "":
		case "-":
			ts.ignored = true
		case "nil", "nilString", "nilList":
			ts.nilOK = true
			if f.Type.Kind() != reflect.Ptr {
				return ts, structTagError{typ, f.Name, t, "field is not a pointer"}
			}
			switch t {
			case "nil":
				ts.nilKind = defaultNilKind(f.Type.Elem())
			case "nilString":
				ts.nilKind = String
			case "nilList":
				ts.nilKind = List
			}
		case "optional":
			ts.optional = true
			if ts.tail {
				return ts, structTagError{typ, f.Name, t, `also has "tail" tag`}
			}
		case "tail":
			ts.tail = true
			if fi != lastPublic {
				return ts, structTagError{typ, f.Name, t, "must be on last field"}
			}
			if ts.optional {
				return ts, structTagError{typ, f.Name, t, `also has "optional" tag`}
			}
			if f.Type.Kind() != reflect.Slice {
				return ts, structTagError{typ, f.Name, t, "field type is not slice"}
			}
		default:
			return ts, fmt.Errorf("rlp: unknown struct tag %q on %v.%s", t, typ, f.Name)
		}
	}
	return ts, nil
}

func structFields(typ reflect.Type) (fields []field, err error) {
	var (
		lastPublic  = lastPublicField(typ)
		anyOptional = false
	)
	for i := 0; i < typ.NumField(); i++ {
		if f := typ.Field(i); f.PkgPath == "" { // exported
			tags, err := parseStructTag(typ, i, lastPublic)
			if err != nil {
				return nil, err
			}
			fmt.Println("no = ", i, "f = ", f, "tags = ", tags)

			// Skip rlp:"-" fields.
			if tags.ignored {
				continue
			}
			// If any field has the "optional" tag, subsequent fields must also have it.
			if tags.optional || tags.tail {
				anyOptional = true
			} else if anyOptional {
				return nil, fmt.Errorf(`rlp: struct field %v.%s needs "optional" tag`, typ, f.Name)
			}
			info := theTC.infoWhileGenerating(f.Type, tags)
			fields = append(fields, field{i, info, tags.optional})
		}
	}
	return fields, nil
}

func cachedDecoder(typ reflect.Type) (decoder, error) {
	fmt.Println("enter cachedDecoder(", typ, ")")
	info := theTC.info(typ)
	return info.decoder, info.decoderErr
}

func Decode(val interface{}) error {
	if val == nil {
		return errDecodeIntoNil
	}
	rval := reflect.ValueOf(val)
	rtyp := rval.Type()
	fmt.Println("rval = ", rval, ", rtyp = ", rtyp)
	fmt.Println("rtyp.Kind() = ", rtyp.Kind(), ", rtyp.Elem() = ", rtyp.Elem())
	fmt.Println("rtyp.Elem().Kind() = ", rtyp.Elem().Kind())

	decoder, err := cachedDecoder(rtyp.Elem())
	if err != nil {
		return err
	}

	decoder(nil, rval.Elem())
	/*
		fields, err := structFields(rtyp.Elem())
		if err != nil {
			fmt.Println("err = ", err)
		}
		for _, f := range fields {
			fmt.Println("field = ", f)
		}
	*/
	return nil
}

func main() {
	bp := new(NewBlockPacket)
	Decode(bp)
}
