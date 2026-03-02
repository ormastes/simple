# Serialization Deep Research: Frameworks, Compiler Formats, and Solution Options

**Date:** 2026-03-01
**Status:** Complete
**Purpose:** Comprehensive serialization research for Simple's header binary + general serialization framework
**Feeds into:** `doc/design/simple_header_binary_design.md`

---

## Part I: General-Purpose Serialization Frameworks (16 Systems)

### 1. Protocol Buffers (Google)

**Wire format:** Tag-value pairs. Tag = `(field_number << 3) | wire_type`. Four wire types: VARINT (0), I64 (1), LEN (2), I32 (5). Integers use LEB128 varint. Signed integers use ZigZag encoding: `(n << 1) ^ (n >> 31)`.

```
# field 1 = string "testing"
0a 07 74 65 73 74 69 6e 67
│  │  └── "testing" UTF-8
│  └── length = 7 (varint)
└── tag: field 1, wire type 2 (LEN) → (1 << 3) | 2 = 0x0a
```

**Schema:** Schema-first. `.proto` files define messages. Not self-describing on wire.
**Type ID:** Integer field tags. Names irrelevant to binary.
**Field skip:** `reserved` keyword for deleted fields. Unknown fields preserved by default (proto3).
**Evolution:** Add optional fields freely. Never reuse tag numbers. Rename freely. Type changes must be wire-compatible.
**Codegen:** Generates language-specific code from `.proto` schema.
**Zero-copy:** No (requires full deserialization).
**Best for:** Cross-language RPC, schema-evolved APIs.

### 2. FlatBuffers (Google)

**Wire format:** Zero-copy buffer with vtable-based access. Root table at buffer start. Each table has a vtable offset, vtable contains field offsets relative to table start. Missing fields have offset 0 in vtable.

```
# Buffer layout (simplified):
[vtable_size:u16] [table_size:u16] [field1_offset:u16] [field2_offset:u16] ...
... [table: vtable_soffset:i32] [field1_data] [field2_data] ...
```

**Schema:** Schema-first (`.fbs` files). Not self-describing.
**Type ID:** Vtable slot position. Field order in schema determines slot.
**Field skip:** Deprecated fields leave vtable slot empty (offset=0).
**Evolution:** Add fields at end. Old readers ignore new vtable slots. Cannot remove or reorder.
**Codegen:** Generates accessors that read directly from buffer.
**Zero-copy:** YES — the key design goal. No deserialization step.
**Best for:** Game engines, performance-critical reads, mmap-friendly.

### 3. Cap'n Proto

**Wire format:** Zero-copy with pointer-based layout. Each struct is a fixed-size data section + pointer section. Pointers encode offset + size. Lists encoded inline. Arena allocation model.

```
# Struct pointer (64 bits):
[offset:30] [data_words:16] [ptr_words:16] [tag:2=0]
# List pointer (64 bits):
[offset:30] [element_size:3] [count:29] [tag:2=1]
```

**Schema:** Schema-first (`.capnp`). Not self-describing.
**Type ID:** Globally unique 64-bit type IDs (random, collision-resistant).
**Field skip:** Promoted to fixed-position slots in data/pointer sections.
**Evolution:** Add fields at end of data/pointer sections. Old code ignores trailing data.
**Codegen:** Generates message builder + reader classes.
**Zero-copy:** YES — in-place access, no parse step. Time-travel RPC.
**Best for:** IPC, low-latency RPC, capability-based security.

### 4. MessagePack

**Wire format:** Self-describing, type-tagged. First byte determines type:

| Range | Type | Example |
|-------|------|---------|
| `0x00-0x7f` | positive fixint | `0x2a` = 42 |
| `0x80-0x8f` | fixmap | `0x82` = map(2 entries) |
| `0x90-0x9f` | fixarray | `0x93` = array(3 items) |
| `0xa0-0xbf` | fixstr | `0xa5` = str(5 bytes) |
| `0xc0` | nil | |
| `0xc2-0xc3` | false/true | |
| `0xcc-0xd3` | uint8-int64 | |
| `0xd9-0xdb` | str 8/16/32 | |
| `0xdc-0xdd` | array 16/32 | |
| `0xde-0xdf` | map 16/32 | |
| `0xe0-0xff` | negative fixint | `0xff` = -1 |

**Schema:** Schema-less. Self-describing.
**Type ID:** Type tag byte in stream. No field names unless in map keys.
**Field skip:** N/A — schema-less, skip by type tag + size.
**Evolution:** N/A — no schema to evolve. Adding keys to maps is inherently flexible.
**Zero-copy:** No.
**Best for:** Compact JSON replacement, dynamic data, logging.

### 5. CBOR (RFC 8949)

**Wire format:** Tag-length-value with 3-bit major type:

| Major | Type | Encoding |
|-------|------|----------|
| 0 | Unsigned int | Additional info = value or length prefix |
| 1 | Negative int | -1 - value |
| 2 | Byte string | Length + bytes |
| 3 | Text string | Length + UTF-8 |
| 4 | Array | Length + items |
| 5 | Map | Length + key-value pairs |
| 6 | Tag | Semantic tag number + content |
| 7 | Simple/float | false, true, null, f16/f32/f64 |

Additional info encoding (5 bits): 0-23 = value inline, 24 = 1-byte, 25 = 2-byte, 26 = 4-byte, 27 = 8-byte, 31 = indefinite length.

**Schema:** Schema-less. Self-describing. CDDL for optional schema.
**Type ID:** Major type + optional tag (major 6). Tag 55799 = self-describing CBOR marker.
**Field skip:** Skip by major type + size. Indefinite-length items use break code (0xFF).
**Evolution:** Schema-less = inherently flexible.
**Zero-copy:** Partial (strings can be referenced in-place).
**Best for:** IoT/constrained devices, COSE/CWT security, deterministic encoding.

### 6. Bincode (Rust)

**Wire format:** Fixed-width, positional. No type tags, no field names. Struct fields serialized in declaration order. Enums: u32 variant index + payload.

```
# struct Point { x: i32, y: i32 }  → Point { x: 42, y: -1 }
2a 00 00 00  ff ff ff ff
│            └── y = -1 (little-endian i32)
└── x = 42 (little-endian i32)
```

**Schema:** Code-first (Rust struct IS the schema). Not self-describing.
**Type ID:** None — pure positional.
**Field skip:** Not possible. Field reorder = data corruption.
**Evolution:** Extremely fragile. Any change breaks format.
**Zero-copy:** No (but very fast decode — minimal overhead).
**Best for:** IPC between identical code versions, checkpointing.

### 7. Postcard (Rust)

**Wire format:** Variable-length encoding (COBS-friendly). Integers use varint. Structs are positional like Bincode but with varint sizes.

**Schema:** Code-first.
**Type ID:** None — positional.
**Field skip:** Not possible.
**Evolution:** Fragile (like Bincode, but variable-length gives minor flexibility).
**Zero-copy:** No.
**Best for:** Embedded systems, `#[no_std]`, constrained memory.

### 8. Apache Avro

**Wire format:** Schema-dependent. No field tags or names in data. Writer schema and reader schema compared at read time. Integers use ZigZag + varint. Strings: length (varint) + UTF-8 bytes.

```
# Schema: {"type":"record","name":"Point","fields":[{"name":"x","type":"long"},{"name":"y","type":"long"}]}
# Point(x=42, y=-1)
54 01
│  └── y = -1 (zigzag varint: 1)
└── x = 42 (zigzag varint: 84 → 54 hex)
```

**Schema:** Schema-first. Schema must accompany data (in file header or out-of-band).
**Type ID:** Schema name + namespace. No in-band field identifiers.
**Field skip:** Reader schema can omit fields → skipped during read. Writer schema can add fields → default used.
**Evolution:** Full schema resolution: compare writer schema vs reader schema field by field. Add/remove fields with defaults. Promote types (int → long → float → double).
**Zero-copy:** No.
**Best for:** Hadoop/data lake, batch analytics, schema registry pattern.

### 9. ASN.1 (BER/DER/PER)

**Wire format (BER/DER):** Tag-Length-Value (TLV). Tag encodes class (2 bits) + constructed (1 bit) + number (5+ bits). Length: short form (1 byte, 0-127) or long form (1 byte count + N bytes).

**Wire format (PER):** Packed. No tags or lengths where schema determines them. Extremely compact.

**Schema:** Schema-first (ASN.1 notation). Very formal.
**Type ID:** OID (Object Identifier) — globally unique dot-notation.
**Field skip:** OPTIONAL and DEFAULT keywords.
**Evolution:** Extension markers (`...`) allow adding fields without breaking old decoders.
**Zero-copy:** PER: partial. BER/DER: no.
**Best for:** Telecom (X.509, SNMP, 5G), formal specifications.

### 10. Erlang ETF (External Term Format)

**Wire format:** Version byte (131) + tagged terms:

| Tag | Type | Layout |
|-----|------|--------|
| 97 | SMALL_INT | 1 byte unsigned |
| 98 | INTEGER | 4 bytes signed |
| 100 | ATOM | 2-byte len + chars |
| 104 | SMALL_TUPLE | 1-byte arity + elements |
| 108 | LIST | 4-byte len + elements + tail |
| 109 | BINARY | 4-byte len + bytes |
| 116 | MAP | 4-byte arity + k/v pairs |

**Schema:** Schema-less. Self-describing.
**Type ID:** Atom string value.
**Field skip:** N/A — unstructured terms.
**Evolution:** Convention: extend tuples, use maps.
**Best for:** Erlang IPC, distributed systems, BEAM ecosystem.

### 11. Python Pickle

**Wire format:** Stack-based VM with opcodes:

| Opcode | Meaning |
|--------|---------|
| `\x80\x05` | Protocol 5 header |
| `K` | SHORT_BININT (1 byte) |
| `X` | SHORT_BINUNICODE (4-byte len + UTF-8) |
| `\x85` | TUPLE1 (pop 1 → tuple) |
| `\x8a` | LONG1 (1-byte len + little-endian bytes) |
| `q` | BINPUT (memo table store) |
| `h` | BINGET (memo table fetch) |
| `.` | STOP |

**Schema:** Schema-less. Self-describing.
**Type ID:** Module + class name string (e.g., `builtins.dict`).
**Field skip:** `__getstate__`/`__setstate__` hooks.
**Evolution:** None. Class must exist at load time.
**Security:** DANGEROUS — arbitrary code execution during load.
**Best for:** Python-only persistence (with trusted data).

### 12. Serde (Rust) — Meta-Framework

**Data model:** 29 abstract types: bool, i8-i128, u8-u128, f32, f64, char, str, bytes, none, some, unit, unit_struct, unit_variant, newtype_struct, newtype_variant, seq, tuple, tuple_struct, tuple_variant, map, struct, struct_variant, enum.

**Design:** Two trait families:
```rust
// Data side (per-type, usually derived)
trait Serialize { fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error>; }
trait Deserialize<'de> { fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error>; }

// Format side (per-format, hand-written)
trait Serializer { fn serialize_struct(...); fn serialize_seq(...); ... }
trait Deserializer { fn deserialize_struct(...); fn deserialize_seq(...); ... }
```

**Key attributes:**
- `#[serde(skip)]` — exclude field both directions
- `#[serde(skip_serializing_if = "Option::is_none")]` — conditional
- `#[serde(rename = "name")]` — wire name
- `#[serde(default)]` — default on missing
- `#[serde(tag = "type")]` — externally tagged enum
- `#[serde(flatten)]` — inline nested struct
- `#[serde(with = "module")]` — custom ser/de module
- `#[serde(deny_unknown_fields)]` — strict mode

**Best for:** Rust ecosystem standard. Format-agnostic serialization.

### 13. Borsh (Near Protocol)

**Wire format:** Deterministic, fixed-width, little-endian. Strings: 4-byte length + UTF-8. Arrays: 4-byte length + elements. Enums: 1-byte variant + payload. **Canonical encoding** — identical input always produces identical bytes (critical for blockchain).

**Schema:** Code-first.
**Type ID:** None — positional.
**Evolution:** Not designed for evolution (blockchain immutability).
**Zero-copy:** No.
**Best for:** Blockchain, cryptographic hashing of structs, consensus protocols.

### 14. rkyv (Rust)

**Wire format:** Zero-copy with "archived" types. Each type has an `Archived<T>` counterpart with identical layout but relative pointers. Buffer is usable in-place without any deserialization.

```rust
#[derive(Archive)]
struct Point { x: i32, y: i32 }
// ArchivedPoint has identical layout: [i32, i32]
// Access: let archived = unsafe { rkyv::archived_root::<Point>(bytes) };
// archived.x is directly readable — no copy, no parse
```

**Schema:** Code-first. Archived type layout determined at compile time.
**Type ID:** None.
**Field skip:** Not applicable (entire struct archived).
**Evolution:** Breaking. Type layout = wire layout.
**Zero-copy:** YES — the primary design goal. Relative pointers for nested data.
**Validation:** Optional validation pass checks pointer bounds.
**Best for:** Fastest possible reads, memory-mapped files, game save states.

### 15. Swift Codable

**Design:** Two protocols:
```swift
protocol Encodable { func encode(to encoder: Encoder) throws }
protocol Decodable { init(from decoder: Decoder) throws }
typealias Codable = Encodable & Decodable
```

**Containers:** Three types — `KeyedContainer` (struct/dict), `UnkeyedContainer` (array), `SingleValueContainer` (scalar). CodingKeys enum maps property names to wire keys.

**Customization:**
```swift
enum CodingKeys: String, CodingKey {
    case firstName = "first_name"  // rename
    // omit property = skip
}
```

**Best for:** Apple platforms, JSON/Plist.

### 16. Kotlin Serialization

**Design:** `@Serializable` annotation triggers compiler plugin (not reflection).

```kotlin
@Serializable
data class Point(
    val x: Int,
    @SerialName("y_coord") val y: Int,
    @Transient val cache: Int = 0  // skipped
)
```

**Generated:** `SerialDescriptor` (schema), `serialize()`, `deserialize()` methods. Polymorphism via `@Polymorphic` annotation + class discriminator.

**Best for:** Kotlin multiplatform, type-safe serialization.

---

## Part II: Compiler-Internal Serialization (10 Systems)

### 1. Rust .rmeta

- **Lazy loading:** `LazyValue<T>` stores byte offset, decodes on access. `LazyTable<I,T>` gives O(1) index lookup.
- **Type encoding:** Shorthand cache — previously-serialized types reuse byte offset.
- **DefId:** `CrateNum` + `DefIndex`. Stable form: `DefPathHash` (128-bit: StableCrateId + path hash).
- **Incremental:** Red/green dep-graph. 128-bit fingerprints via `HashStable`. Query-level granularity.

### 2. LLVM Bitcode

- **Bitstream container:** Stream of bits, LSB-first. Blocks with abbreviation scopes.
- **Abbreviations:** Custom encodings per block. `DEFINE_ABBREV` specifies field widths (Fixed, VBR, Array, Char6, Blob). 22% smaller than text IR.
- **Records:** `UNABBREV_RECORD` (general) or abbreviated (compact).
- **Blocks:** MODULE_BLOCK → TYPE_BLOCK, FUNCTION_BLOCK, CONSTANTS_BLOCK, etc.

### 3. GHC .hi Files

- **Contents:** Export list, type signatures, typeclass instances, rewrite rules, inlining templates.
- **Encoding:** Custom `Binary` class with LEB128 integers. Dictionary deduplication for strings.
- **Fingerprinting:** Per-declaration MD5. Module ABI hash. File only rewritten if changed → prevents cascade.

### 4. OCaml .cmi

- **Format:** Marshal module output. Tag-based: `PREFIX_SMALL_INT`, `CODE_INT8/16/32/64`, `PREFIX_SMALL_BLOCK`.
- **Sharing:** Hash table detects already-serialized values → back-reference. Handles cycles.
- **Magic:** `Caml1999I0XX` where `XX` is version.

### 5. Go Unified IR Export

- **10 sections:** SectionString, SectionPkg, SectionBody, SectionMeta, SectionType, SectionName, SectionObj, SectionPosBase, SectionObjExt, SectionObjDict.
- **Footer:** 8-byte SHA-256 fingerprint for cache validation.
- **Lazy:** Index enables jumping to specific declarations.

### 6. Swift .swiftmodule

- **Container:** LLVM bitstream format (reused).
- **Blocks:** CONTROL_BLOCK, INPUT_BLOCK, SIL_BLOCK, AST_BLOCK, IDENTIFIER_BLOCK, INDEX_BLOCK.
- **Text alternative:** `.swiftinterface` — human-readable, compiler-version-stable.

### 7. Clang PCH/Modules

- **Container:** LLVM bitstream in `__clangast` section.
- **RPN expressions:** Subexpressions stored in reverse order, stack-based decode.
- **Lazy:** Types, declarations, macros all load on-demand via `ExternalASTSource`.
- **IDs:** TypeID, DeclID, IdentifierID — numeric indices.
- **Chained PCH/Modules:** ID numbering continues from predecessor. DAG support for modules.

### 8. Java .class Constant Pool

- **Layout:** 1-indexed table after magic `0xCAFEBABE`. Each entry: tag byte + fields.
- **Deduplication:** Multiple refs share same `Utf8` entry. `NameAndType` sharing.
- **Generics:** Preserved in `Signature` attribute (erased from bytecode).

### 9. V8 Snapshot

- **Format:** Serializer VM with bytecodes (`kNewObject`, `kBackref`, `kRootArray`).
- **Code cache header:** magic + version_hash + source_hash + flag_hash + payload_length + checksum.
- **Lazy:** Only 30% of built-ins loaded eagerly. `DeserializeLazy` handler on first call.

### 10. Dart .dill

- **Tag-based AST:** Each node has a tag byte (Expressions 20-120, Statements 61-76, Types 90-100).
- **VarInt:** UInt7/UInt14/UInt30 (2-bit prefix in high bits).
- **Strings:** WTF-8 blob with end-offset array — O(1) lookup by index.
- **Names:** Hierarchical `CanonicalName` tree (parent index chain).
- **Random access:** Byte-offset arrays for libraries/classes/procedures.

---

## Part III: Existing Simple Infrastructure

### Already Implemented

| Component | Location | Capability |
|-----------|----------|------------|
| **Serializable trait** | `src/lib/nogc_sync_mut/binary_io.spl` | `trait Serializable`, `trait Deserializable`, `BinaryWriter`, `BinaryReader`, `ByteOrder` enum |
| **Varint encoding** | `src/lib/common/serialization/serialize.spl` | `write_varint()`, `read_varint()`, type-tagged serialization |
| **Type utilities** | `src/lib/common/serialization/utilities.spl` | `tag_type()`, `add_version()`, `structural_hash_*()`, hex conversion |
| **SDN format** | `src/lib/common/sdn/` | `SdnValue` enum, parse/serialize, tables |
| **JSON** | `src/lib/common/json/` | Full encode/decode |
| **CBOR** | `src/lib/common/cbor/` | Major type system, encode/decode |
| **MessagePack** | `src/lib/common/msgpack/` | Full encode/decode |
| **Protobuf** | `src/lib/common/protobuf/` | Varint, ZigZag, field-tagged encoding |
| **Avro** | `src/lib/common/avro/` | ZigZag varint, schema support |
| **MIR serialization** | `src/compiler/50.mir/mir_serialization.spl` | 50+ instruction types → JSON |
| **HIR serialization** | `src/compiler/20.hir/inference/serialize.spl` | Type hints → SDN tables |
| **SMF format** | `src/compiler/70.backend/linker/` | 128-byte header, sections, symbols, string table, compression |
| **ELF writer** | `src/compiler/70.backend/backend/native/` | Full ELF64 generation |
| **API surface** | `src/compiler/90.tools/api_surface.spl` | Public symbol tracking, diff |
| **Incremental** | `src/compiler/80.driver/incremental.spl` | Hash-based dirty tracking |

### Missing Pieces

1. No annotation system (`@skip`, `@serial_id`) — requires parser changes
2. No automatic derive/codegen for struct serialization
3. No reflection API for runtime field iteration
4. No schema definition language
5. No zero-copy deserialization support

---

## Part IV: Comparative Matrix

### Format Comparison

| Format | Self-Describing | Schema | Zero-Copy | Evolution | Compactness | Speed |
|--------|:-:|:-:|:-:|:-:|:-:|:-:|
| Protobuf | No | `.proto` file | No | Strong | High | Fast |
| FlatBuffers | No | `.fbs` file | YES | Moderate | Moderate | Fastest read |
| Cap'n Proto | No | `.capnp` file | YES | Moderate | Moderate | Fastest read |
| MessagePack | Yes | None | No | N/A | High | Fast |
| CBOR | Yes | Optional CDDL | Partial | N/A | High | Fast |
| Bincode | No | Code-first | No | None | Highest | Fastest |
| Avro | With schema | `.avsc` file | No | Strong | Highest | Fast |
| ASN.1 PER | No | ASN.1 notation | Partial | Strong | Highest | Moderate |
| Erlang ETF | Yes | None | No | N/A | Low | Moderate |
| Borsh | No | Code-first | No | None | High | Fast |
| rkyv | No | Code-first | YES | None | Moderate | Fastest |
| Serde | Depends on format | Code-first | Depends | Depends | Depends | Fast |

### Compiler Format Comparison

| Compiler | Container | Lazy Load | Type ID | String Dedup | Fingerprint | Evolution |
|----------|-----------|:-:|---------|:-:|:-:|:-:|
| Rust .rmeta | Custom binary | YES | DefId (hash+idx) | Yes | 128-bit SipHash | Yes |
| LLVM .bc | Bitstream | Block-skip | Type table index | STRTAB blob | No | Abbrev versioning |
| GHC .hi | Custom Binary | Partial | OccName | Dictionary | MD5 per-decl | Yes |
| Go export | 10-section | YES | Package path | SectionString | SHA-256 footer | Yes |
| Swift .swiftmodule | LLVM bitstream | YES | DeclID/TypeID | IDENTIFIER blob | No | Version check |
| Clang PCH | LLVM bitstream | YES | TypeID/DeclID | On-disk hash | No | Chained |
| Java .class | Constant pool | No | FQ class name | Pool dedup | No | serialVersionUID |
| Dart .dill | Tag-based | YES | Canonical name | WTF-8 blob | No | Version check |

---

## Part V: Solution Options for Simple

Below are **5 concrete solutions**. Each is self-contained and implementable independently.

---

### Solution A: "Protobuf-Style" — Tagged Field Binary

**Inspiration:** Protocol Buffers + Serde attributes

**Core idea:** Each serialized field carries a `(tag_number, wire_type, value)` triple. Tags are stable integers assigned by annotation or auto-assignment. Unknown tags are skipped. Fields can be added/removed freely.

**Wire format:**
```
[tag:varint] [wire_type:3bits from tag] [value...]

Wire types:
  0 = varint (i64, bool, enum variant)
  1 = fixed64 (f64, u64)
  2 = length-delimited (text, bytes, nested struct, array)
  5 = fixed32 (f32, u32)
```

**Annotations:**
```simple
@serialize
struct Point:
    @tag(1) x: f64
    @tag(2) y: f64
    @skip   cached_mag: f64?
    @tag(3) @default(0.0) z: f64
```

**Generated code pattern:**
```simple
impl Serializable for Point:
    fn serialize(w: BinaryWriter):
        w.write_tag(1, WIRE_FIXED64)
        w.write_f64(self.x)
        w.write_tag(2, WIRE_FIXED64)
        w.write_f64(self.y)
        # cached_mag skipped
        if self.z != 0.0:
            w.write_tag(3, WIRE_FIXED64)
            w.write_f64(self.z)

    static fn deserialize(r: BinaryReader) -> Point?:
        var x = 0.0; var y = 0.0; var z = 0.0
        while r.remaining() > 0:
            val tag = r.read_varint()
            val field = tag >> 3
            val wire = tag & 0x07
            match field:
                1: x = r.read_f64()
                2: y = r.read_f64()
                3: z = r.read_f64()
                _: r.skip_field(wire)  # forward-compat
        Point(x: x, y: y, z: z, cached_mag: nil)
```

**Header format:** Section-based binary (like current SMF) with string table. Each section is a protobuf-style tagged stream.

**Pros:**
- Proven at massive scale (Google, gRPC ecosystem)
- Strong schema evolution (add/remove fields freely)
- Existing protobuf encoder in `src/lib/common/protobuf/` to build on
- Self-documenting tag numbers
- Forward and backward compatible

**Cons:**
- Tag overhead per field (~1-2 bytes each)
- Not zero-copy
- Requires annotation parsing (`@tag(N)`)
- More complex than positional encoding

**Implementation effort:** Medium. Reuse existing protobuf varint/zigzag. Add `@tag`/`@skip` annotation parsing. Generate serialize/deserialize from struct definitions.

---

### Solution B: "FlatBuffer-Style" — Zero-Copy with VTable

**Inspiration:** FlatBuffers + rkyv

**Core idea:** Structs serialized with a vtable that maps field slots to byte offsets. Data read directly from the buffer without copying. Missing fields have offset 0 → default value.

**Wire format:**
```
┌─────────────────────────────┐
│ VTable                      │
│   vtable_size: u16          │
│   object_size: u16          │
│   field_0_offset: u16       │  ← 0 = field absent
│   field_1_offset: u16       │
│   ...                       │
├─────────────────────────────┤
│ Object Data                 │
│   vtable_offset: i32 (neg)  │  ← points back to vtable
│   field data (inline)       │
│   ...                       │
└─────────────────────────────┘
```

**Annotations:**
```simple
@flatbuf
struct Point:
    @id(0) x: f64       # vtable slot 0
    @id(1) y: f64       # vtable slot 1
    @id(2) z: f64       # vtable slot 2 (can add later)
    @skip  cache: f64?  # not in vtable
```

**Access pattern (zero-copy):**
```simple
fn get_x(buf: [u8], obj_offset: i64) -> f64:
    val vtable_offset = read_i32(buf, obj_offset)
    val vtable_start = obj_offset - vtable_offset
    val field_offset = read_u16(buf, vtable_start + 4 + 0 * 2)  # slot 0
    if field_offset == 0: return 0.0  # default
    read_f64(buf, obj_offset + field_offset)
```

**Header format:** Entire `.shb` file is a single FlatBuffer-like buffer. Root table = module interface. Nested tables for functions, structs, etc. String table embedded as shared strings.

**Pros:**
- Zero deserialization cost — read directly from mmap'd file
- Fastest possible read performance
- Good evolution (add fields by extending vtable)
- Existing BinaryReader/BinaryWriter in `binary_io.spl`
- Ideal for header files loaded frequently

**Cons:**
- Complex implementation (vtable management, offset calculation)
- Write is slower (must build buffer bottom-up)
- Harder to debug (binary, not self-describing)
- Larger file size than tagged formats (vtable overhead)
- Cannot handle variable-length inline data easily

**Implementation effort:** High. Requires buffer builder, vtable deduplication, offset tracking. But payoff is fastest possible reads.

---

### Solution C: "Dart/LLVM-Style" — Tag-Byte AST Serialization

**Inspiration:** Dart .dill + LLVM bitstream + Clang PCH

**Core idea:** Each AST node type gets a unique tag byte. Serialization walks the tree, emitting tag + fields. Variable-length integers (like Dart's UInt7/14/30). String table with index-based references. Offset table for random access.

**Wire format:**
```
[magic: "SHB\0"]
[version: u16]
[string_count: varint]
[strings: length-prefixed UTF-8 blob with end-offset array]
[symbol_count: varint]
[offset_table: [u32] × symbol_count]  ← random access
[body: tag-byte stream]
  TAG_FUNCTION (0x01) [name_idx:varint] [param_count:varint] [ret_type_idx:varint] [flags:u8]
    TAG_PARAM (0x10) [name_idx:varint] [type_idx:varint] [flags:u8]
    TAG_PARAM (0x10) ...
    TAG_END (0xFF)
  TAG_STRUCT (0x02) [name_idx:varint] [field_count:varint] [class_hash:u64]
    TAG_FIELD (0x11) [name_idx:varint] [type_idx:varint] [serial_id:varint] [flags:u8]
    ...
    TAG_END (0xFF)
  TAG_ENUM (0x03) ...
  TAG_TRAIT (0x04) ...
```

**Tag byte allocation:**
```
0x01-0x0F: Top-level declarations (fn, struct, class, enum, trait, alias, const, import, export)
0x10-0x1F: Sub-elements (param, field, variant, method_ref, generic_param, constraint)
0x20-0x2F: Type references (named, generic_inst, function_type, array_type, optional_type)
0x30-0x3F: Annotation entries (serial_id, skip, default, rename)
0xFE:      Section marker
0xFF:      End marker
```

**String table (Dart-inspired):**
```
[end_offsets: u32 × count]
[blob: UTF-8 bytes concatenated]

String N spans blob[end_offsets[N-1]..end_offsets[N]]
O(1) lookup by index. No null terminators.
```

**Annotations (inline in stream):**
```simple
@serialize
struct Point:
    @serial_id(1) x: f64
    @serial_id(2) y: f64
    @skip cached: f64?
```

Serialized as:
```
TAG_STRUCT [name_idx] [field_count=2] [hash]
  TAG_ANNOTATION_SERIAL_ID [1]
  TAG_FIELD [name_idx="x"] [type_idx="f64"] [flags]
  TAG_ANNOTATION_SERIAL_ID [2]
  TAG_FIELD [name_idx="y"] [type_idx="f64"] [flags]
  TAG_END
```

**Pros:**
- Matches what compilers actually do (Dart, Clang, Swift all use this)
- Natural fit for AST data (tree structure → tag-byte stream)
- Compact (varint + string interning)
- Random access via offset table
- Extensible (new tag bytes for new node types)
- String table pattern already used in SMF

**Cons:**
- Not zero-copy (must decode varint, look up strings)
- Schema evolution requires careful tag allocation
- More complex than pure positional encoding
- Custom format (no ecosystem tooling)

**Implementation effort:** Medium. String table and varint already exist. Tag-byte walker is straightforward. Offset table is new but simple.

---

### Solution D: "SDN-Native" — Text-First with Binary Cache

**Inspiration:** Avro (schema accompanies data) + TypeScript .d.ts + GHC fingerprinting

**Core idea:** The **primary format is SDN** (human-readable, diffable, versionable). A binary cache (`.shb.cache`) is auto-generated for speed but always derivable from the SDN. The SDN file IS the source of truth.

**SDN format (`.shd` — Simple Header Declaration):**
```sdn
# Simple Header Declaration: math.vector
# Version: 1
# Interface Hash: 0xA1B2C3D4E5F60718

module = "math.vector"

functions |name, serial_id, params, return_type, flags|
    "dot",      1, "(a: Vector, b: Vector)", "f64",     ""
    "cross",    2, "(a: Vector3, b: Vector3)", "Vector3", ""
    "normalize",3, "(v: Vector)", "Vector",    ""

structs |name, serial_id, class_hash, generics|
    "Vector",  1, "0xABCD1234", ""
    "Vector3", 2, "0xDEADBEEF", ""

fields |parent, name, serial_id, type, flags|
    "Vector",  "x", 1, "f64", "pub"
    "Vector",  "y", 2, "f64", "pub"
    "Vector",  "z", 3, "f64", "pub,default=0.0"
    "Vector3", "x", 1, "f64", "pub"
    "Vector3", "y", 2, "f64", "pub"
    "Vector3", "z", 3, "f64", "pub"

traits |name, serial_id, required, default_methods|
    "Numeric", 1, "add,sub,mul", "sum"

imports |module, symbols|
    "std.math", "sqrt,atan2"

exports |name, kind, serial_id|
    "Vector",    "struct", 1
    "dot",       "fn",     1
    "cross",     "fn",     2
    "Numeric",   "trait",  1
```

**Binary cache (`.shb.cache`):** Auto-generated from `.shd` using any fast binary encoding (could be CBOR, MessagePack, or simple positional). Invalidated by file hash comparison.

**Annotations:**
```simple
@serial_id(1)
struct Point:
    @serial_id(1) x: f64
    @serial_id(2) y: f64
    @skip cached: f64?
```

**Fingerprinting (GHC-inspired):** Per-declaration hash. Module hash = combine(all declaration hashes). `.shd` file only rewritten if module hash changes → prevents rebuild cascade (GHC's key optimization).

**Pros:**
- Human-readable, git-diffable, reviewable
- SDN infrastructure already fully built
- SDN table format perfect for flat symbol lists
- Familiar to anyone who reads SDN
- Binary cache gives speed when needed
- Easiest to debug and test
- `hints_to_sdn()` / `hints_from_sdn()` pattern already exists in HIR

**Cons:**
- Slower than binary-first approaches (parse text → build structures)
- Binary cache adds complexity (invalidation, generation)
- SDN tables are flat — nested structures (generic constraints, method params) need encoding tricks
- Larger file size than binary
- No zero-copy

**Implementation effort:** Low-Medium. SDN writer/reader exist. Table format exists. Main work: extract header AST → emit SDN tables.

---

### Solution E: "Hybrid Chunk" — SMF-Compatible Binary Sections

**Inspiration:** Erlang BEAM chunks + existing SMF format + Rust .rmeta lazy tables

**Core idea:** Reuse the existing SMF section-table architecture. Add new section types for header data. The `.shb` file is literally a simplified SMF file with header-only sections. This means the SMF reader/writer code can be reused directly.

**Wire format:** Exactly like SMF but with new section types:

```
┌─────────────────────────────────────┐
│ Sections                            │
│   STRTAB: String table              │
│   FUNC_SIG: Function signatures     │
│   TYPE_DEF: Struct/class/enum defs  │
│   TRAIT_DEF: Trait definitions      │
│   GENERIC_META: Generic constraints │
│   IMPORT_DEP: Dependencies          │
│   EXPORT_MAP: Re-exports            │
│   SERIAL_MAP: Serial ID mappings    │
│   IFACE_HASH: Interface fingerprint │
├─────────────────────────────────────┤
│ Section Table                       │
├─────────────────────────────────────┤
│ Header (128 bytes at EOF-128)       │
│   magic: "SHB\0"                    │
│   version, flags, counts            │
│   interface_hash, source_hash       │
│   section_count, section_table_off  │
└─────────────────────────────────────┘
```

**Section internals:** Each section uses a flat record format:

```
# FUNC_SIG section: array of fixed-header + variable-length entries
[entry_count: u32]
[offset_table: u32 × entry_count]  ← for random access (like Rust LazyTable)
[entries...]
  Entry:
    [name_strtab_idx: u32]
    [serial_id: u32]
    [flags: u16]
    [param_count: u16]
    [return_type_strtab_idx: u32]
    [generic_count: u8]
    [reserved: u8 × 3]
    [params: (name_idx: u32, type_idx: u32, flags: u8, pad: u8×3) × param_count]
    [generics: (name_idx: u32, constraint_idx: u32) × generic_count]
```

**Annotations:**
```simple
@serial_id(1)
struct Point:
    @serial_id(1) x: f64
    @serial_id(2) y: f64
    @skip cached: f64?
```

**Lazy loading (Rust .rmeta inspired):** Offset table at section start enables O(1) jump to any entry. Only decode entries actually referenced by downstream compilation.

**Pros:**
- Reuses ~70K lines of existing SMF infrastructure
- Same 128-byte trailer header pattern (proven)
- Same string table pattern (proven)
- Same section table pattern (proven)
- Same byte-level utilities (proven)
- Lazy loading via offset tables
- Can embed `.shb` sections directly inside `.smf` files (no separate file needed)
- Consistent tooling (SMF reader/dumper works on both)

**Cons:**
- Tied to SMF architecture choices (128-byte header may be overkill for headers)
- Not self-describing (requires reader to know section layouts)
- More rigid than tag-byte format (fixed record sizes per section)
- Not human-readable

**Implementation effort:** Low. Mostly new section type definitions + extraction logic. Reader/writer patterns are copy-paste from existing SMF code.

---

## Comparison of Solutions

| Aspect | A: Protobuf-Style | B: FlatBuf-Style | C: Dart/LLVM-Style | D: SDN-Native | E: Hybrid Chunk |
|--------|:-:|:-:|:-:|:-:|:-:|
| **Read speed** | Fast | Fastest | Fast | Moderate | Fast |
| **Write speed** | Fast | Slow | Fast | Fast | Fast |
| **Zero-copy** | No | YES | No | No | Partial (mmap) |
| **Self-describing** | No | No | No | YES | No |
| **Human-readable** | No | No | No | YES | No |
| **Schema evolution** | Strong | Moderate | Moderate | Strong | Moderate |
| **Existing code reuse** | protobuf encoder | BinaryWriter | varint + strtab | SDN + tables | SMF infra |
| **Implementation effort** | Medium | High | Medium | Low-Medium | Low |
| **File size** | Small | Medium | Small | Large | Medium |
| **Debuggability** | Low | Low | Low | High | Low |
| **Random access** | No | Yes (vtable) | Yes (offset table) | No | Yes (offset table) |
| **Embeddable in SMF** | No | No | No | Yes (note.sdn) | YES (native) |
| **Git-diffable** | No | No | No | YES | No |

### Recommended Combinations

These solutions are not mutually exclusive. Recommended pairings:

| Combination | Description | Use Case |
|-------------|-------------|----------|
| **D + E** | SDN as primary interface + SMF sections for compiled cache | Best of both: human-readable source + fast binary |
| **C + D** | Tag-byte binary + SDN companion | Like current MIR approach (binary + JSON debug) |
| **A + D** | Protobuf-tagged binary + SDN companion | Strong evolution + readability |
| **E alone** | Pure SMF-compatible chunks | Simplest implementation, reuses most code |
| **D alone** | Pure SDN text | Simplest to implement, debug, and test |

---

## References

- [Protocol Buffers Encoding](https://protobuf.dev/programming-guides/encoding/)
- [FlatBuffers Internals](https://flatbuffers.dev/flatbuffers_internals.html)
- [Cap'n Proto Encoding](https://capnproto.org/encoding.html)
- [MessagePack Spec](https://github.com/msgpack/msgpack/blob/master/spec.md)
- [CBOR RFC 8949](https://www.rfc-editor.org/rfc/rfc8949)
- [Serde Data Model](https://serde.rs/data-model.html)
- [rkyv Architecture](https://rkyv.org/architecture.html)
- [LLVM Bitcode Format](https://llvm.org/docs/BitCodeFormat.html)
- [Rust Compiler Serialization](https://rustc-dev-guide.rust-lang.org/serialization.html)
- [GHC Recompilation Avoidance](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/recompilation-avoidance)
- [Go Unified IR](https://internals-for-interns.com/posts/go-compiler-unified-ir/)
- [Swift Serialization](https://github.com/swiftlang/swift/blob/main/docs/Serialization.md)
- [Clang PCH Internals](https://clang.llvm.org/docs/PCHInternals.html)
- [Dart Kernel Binary Format](https://github.com/dart-lang/sdk/blob/main/pkg/kernel/binary.md)
- [Kotlin Serialization Guide](https://kotlinlang.org/docs/serialization.html)
- [Borsh Specification](https://borsh.io/)
- [Apache Avro Specification](https://avro.apache.org/docs/current/specification/)
