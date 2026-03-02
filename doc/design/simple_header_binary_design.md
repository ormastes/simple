# Simple Header Binary (.shb) and AST Serialization Design

**Date:** 2026-03-01
**Status:** Draft
**Requirements:** Incremental compilation, watcher AST header generation, module interface caching
**Research:** Cross-language serialization study (Zig, Rust, Erlang, Java, Ruby, TypeScript)
**Related:** `doc/design/smf_note_sdn_implementation.md`, `src/compiler/90.tools/api_surface.spl`

---

## Problem Statement

The current watcher (`src/compiler/80.driver/build/watch.spl`) only generates SMF files on change. Downstream modules must re-parse full source files to resolve types, functions, and signatures — even when the public interface hasn't changed. This creates two problems:

1. **Redundant parsing** — Dependent modules re-parse source even if only internal code changed
2. **No interface cache** — No binary representation of a module's public API surface for fast loading

**Goal:** Generate a parsed AST header file (`.shb` — Simple Header Binary) that captures the public interface of a module. Dependents load the `.shb` instead of re-parsing full source when the interface hasn't changed.

**Sub-goals:**
- Define a serialization framework that supports binary and SDN output
- Support type identification by object ID, serial ID, and class hash
- Allow field skipping and customization annotations
- Define the `.shb` format as a C-header-like interface file for Simple modules

---

## Cross-Language Research Summary

Six languages were studied for their serialization and module interface approaches:

| Language | Interface Format | Type ID Method | Field Skip | Versioning |
|----------|-----------------|----------------|------------|------------|
| **Zig** | Same `.zig` file (pub decls) | Structural (comptime) | comptime filter | Manual |
| **Rust** | `.rmeta` binary (auto-gen) | DefId (hash+index) | `#[serde(skip)]` | Fingerprints |
| **Erlang** | `.hrl` text + `ExpT` chunk | Atom string | Manual | Convention |
| **Java** | `.class` binary | FQ class name + `serialVersionUID` | `transient` keyword | UID hash |
| **Ruby** | `.rbi` text stubs (Sorbet) | Class name string | `marshal_dump` | Manual |
| **TypeScript** | `.d.ts` text (auto-gen) | Structural (interfaces) | `?:` optional | Semver |

### Key Design Insights

1. **Protobuf-style tag IDs** are the most robust for binary evolution — decouple wire format from names
2. **Separate interface files** (Rust `.rmeta`, TS `.d.ts`) enable faster downstream compilation
3. **Dual format** (binary + text) is common — binary for speed, text for debugging
4. **Serde's attribute model** (`skip`, `rename`, `default`) is the most ergonomic field customization
5. **Java's `serialVersionUID`** (hash of class structure) catches incompatible changes automatically
6. **Content-hash caching** (Zig, TypeScript `.tsbuildinfo`) is the standard for incremental builds

### Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Interface separation | Separate `.shb` file | Avoids re-parsing source; matches Rust/TS pattern |
| Primary format | Binary with SDN companion | Binary for speed; SDN for debugging/diffing |
| Type identification | Triple: obj_id + serial_id + class_hash | Covers positional, stable, and structural identity |
| Field customization | Annotation-driven (`@skip`, `@serial_id`) | Matches Serde ergonomics, fits Simple's syntax |
| Versioning | Content hash + format version | Automatic invalidation like Zig/Rust |
| Header structure | Chunk-based (like SMF/BEAM) | Proven pattern, already used in SMF |

---

## Architecture

### System Overview

```
Source File (.spl)
    │
    ├─[Parser]──→ Full AST
    │                │
    │                ├─[Header Extractor]──→ Header AST (public-only)
    │                │                          │
    │                │                          ├─[SHB Writer]──→ .shb (binary)
    │                │                          └─[SDN Writer]──→ .shd (text)
    │                │
    │                └─[Compiler Pipeline]──→ MIR → Backend → SMF/ELF
    │
    └─[Watcher]──→ On change: re-parse → compare header hash → skip if unchanged
```

### File Layout

```
project/
├── src/
│   └── lib/
│       └── math/
│           ├── vector.spl          # Source
│           └── matrix.spl          # Source
├── .build/
│   └── headers/
│       └── lib/
│           └── math/
│               ├── vector.shb      # Binary header (fast load)
│               ├── vector.shd      # SDN header (debuggable)
│               ├── matrix.shb
│               └── matrix.shd
└── .build/
    └── smf/
        └── lib/math/
            ├── vector.smf          # Compiled module
            └── matrix.smf
```

---

## SHB Binary Format

### Header (64 bytes)

```
┌───────────────────────────────────────────────────────────────┐
│ Identification (8 bytes)                                      │
│   magic[4]       "SHB\0" (0x53484200)                         │
│   version_major   u8 (1)                                      │
│   version_minor   u8 (0)                                      │
│   flags           u16                                         │
├───────────────────────────────────────────────────────────────┤
│ Counts (16 bytes)                                             │
│   section_count    u16                                        │
│   symbol_count     u32                                        │
│   string_table_size u32                                       │
│   reserved         [u8; 6]                                    │
├───────────────────────────────────────────────────────────────┤
│ Hashing (24 bytes)                                            │
│   interface_hash   u64   # Hash of public API surface         │
│   source_hash      u64   # Hash of source file content        │
│   dependency_hash  u64   # Hash of all dependency interfaces  │
├───────────────────────────────────────────────────────────────┤
│ Module Info (16 bytes)                                        │
│   module_path_idx  u32   # Index into string table            │
│   source_path_idx  u32   # Index into string table            │
│   reserved         [u8; 8]                                    │
└───────────────────────────────────────────────────────────────┘
```

**Flags:**
```
SHB_FLAG_HAS_GENERICS   = 0x0001   # Module exports generic types
SHB_FLAG_HAS_TRAITS     = 0x0002   # Module exports traits
SHB_FLAG_HAS_MACROS     = 0x0004   # Module exports macros/mixins
SHB_FLAG_HAS_REEXPORTS  = 0x0008   # Module re-exports from dependencies
SHB_FLAG_COMPRESSED     = 0x0010   # Sections are zstd-compressed
```

### Section Table

Each section entry (16 bytes):

```
┌────────────────────────────────────────┐
│ section_type   u16                     │
│ flags          u16                     │
│ offset         u32                     │
│ size           u32                     │
│ entry_count    u32                     │
└────────────────────────────────────────┘
```

**Section Types:**

| Type | ID | Contents |
|------|----|----------|
| `STRTAB` | 0x01 | String table — all names interned |
| `FUNCTIONS` | 0x02 | Public function signatures |
| `STRUCTS` | 0x03 | Public struct definitions |
| `CLASSES` | 0x04 | Public class definitions |
| `ENUMS` | 0x05 | Public enum definitions |
| `TRAITS` | 0x06 | Public trait definitions |
| `GENERICS` | 0x07 | Generic parameter constraints |
| `IMPORTS` | 0x08 | Module dependency list |
| `EXPORTS` | 0x09 | Re-export mappings |
| `TYPE_ALIASES` | 0x0A | Type alias definitions |
| `CONSTANTS` | 0x0B | Public constant values |
| `SERIAL_MAP` | 0x0C | Serial ID ↔ symbol mapping |

### String Table (Section Type 0x01)

All names are deduplicated and stored once:

```
offset 0:  "math.vector\0"
offset 12: "Point\0"
offset 18: "x\0"
offset 20: "y\0"
offset 22: "z\0"
offset 24: "i64\0"
offset 28: "add\0"
offset 32: "scale\0"
...
```

Symbols reference names by u32 offset into this table, like ELF `.strtab`.

### Function Entry (Variable Length)

```
┌────────────────────────────────────────┐
│ name_idx        u32  # String table    │
│ serial_id       u32  # Stable ID       │
│ flags           u16                    │
│ param_count     u16                    │
│ return_type_idx u32  # String table    │
│ generic_count   u8                     │
│ reserved        [u8; 3]               │
├────────────────────────────────────────┤
│ For each param:                        │
│   param_name_idx   u32                 │
│   param_type_idx   u32                 │
│   param_flags      u8  (default, etc.) │
│   reserved         [u8; 3]            │
├────────────────────────────────────────┤
│ For each generic:                      │
│   type_param_idx   u32  # Name         │
│   constraint_idx   u32  # Bound type   │
└────────────────────────────────────────┘
```

**Function Flags:**
```
FN_FLAG_ASYNC      = 0x0001
FN_FLAG_GENERATOR  = 0x0002
FN_FLAG_STATIC     = 0x0004
FN_FLAG_MUTABLE    = 0x0008   # 'me' method
FN_FLAG_OPERATOR   = 0x0010
FN_FLAG_CONST      = 0x0020
```

### Struct/Class Entry (Variable Length)

```
┌────────────────────────────────────────┐
│ name_idx        u32  # String table    │
│ serial_id       u32  # Stable ID       │
│ class_hash      u64  # FNV-1a of shape │
│ field_count     u16                    │
│ method_count    u16                    │
│ generic_count   u8                     │
│ flags           u8                     │
│ reserved        [u8; 2]               │
├────────────────────────────────────────┤
│ For each field:                        │
│   field_name_idx   u32                 │
│   field_type_idx   u32                 │
│   field_serial_id  u32                 │
│   field_flags      u8                  │
│   reserved         [u8; 3]            │
├────────────────────────────────────────┤
│ For each method:                       │
│   method_func_idx  u32  # -> FUNCTIONS │
├────────────────────────────────────────┤
│ For each generic:                      │
│   type_param_idx   u32                 │
│   constraint_idx   u32                 │
└────────────────────────────────────────┘
```

**Field Flags:**
```
FIELD_FLAG_PUBLIC   = 0x01
FIELD_FLAG_MUTABLE  = 0x02
FIELD_FLAG_OPTIONAL = 0x04
FIELD_FLAG_DEFAULT  = 0x08   # Has default value
FIELD_FLAG_SKIP     = 0x10   # @skip — excluded from serialization
```

### Enum Entry

```
┌────────────────────────────────────────┐
│ name_idx        u32                    │
│ serial_id       u32                    │
│ variant_count   u16                    │
│ generic_count   u8                     │
│ reserved        [u8; 5]               │
├────────────────────────────────────────┤
│ For each variant:                      │
│   variant_name_idx u32                 │
│   variant_serial_id u32               │
│   payload_type_idx u32  # 0 = no data  │
└────────────────────────────────────────┘
```

### Trait Entry

```
┌────────────────────────────────────────┐
│ name_idx           u32                 │
│ serial_id          u32                 │
│ required_count     u16  # Must impl    │
│ default_count      u16  # Has default  │
│ assoc_type_count   u8                  │
│ generic_count      u8                  │
│ reserved           [u8; 2]            │
├────────────────────────────────────────┤
│ For each required method:              │
│   method_func_idx  u32  # -> FUNCTIONS │
├────────────────────────────────────────┤
│ For each default method:               │
│   method_func_idx  u32  # -> FUNCTIONS │
├────────────────────────────────────────┤
│ For each associated type:              │
│   assoc_name_idx   u32                 │
│   bound_type_idx   u32                 │
└────────────────────────────────────────┘
```

### Serial Map (Section Type 0x0C)

Maps stable serial IDs to symbol names for evolution:

```
┌────────────────────────────────────────┐
│ For each mapping:                      │
│   serial_id     u32                    │
│   name_idx      u32   # String table   │
│   kind          u8    # fn/struct/etc.  │
│   reserved      [u8; 3]               │
└────────────────────────────────────────┘
```

---

## Serialization Framework

### Three-Tier Type Identification

Every serializable symbol carries three identifiers:

```
┌──────────────────────────────────────────────────────────────────┐
│ obj_id       Positional index within the header section.         │
│              Fast O(1) lookup. Changes on reorder.               │
│                                                                  │
│ serial_id    Stable numeric ID assigned at definition.           │
│              Assigned once, never changes. Survives reorder      │
│              and rename. Like Protobuf field tags.                │
│              Annotation: @serial_id(42)                          │
│              Auto-assigned: next available if not specified.      │
│                                                                  │
│ class_hash   FNV-1a hash of the structural shape:                │
│              hash(name + field_names + field_types + method_sigs) │
│              Detects incompatible structural changes.             │
│              Like Java's serialVersionUID.                        │
└──────────────────────────────────────────────────────────────────┘
```

**Usage by context:**

| Context | ID Used | Rationale |
|---------|---------|-----------|
| Binary `.shb` internal refs | `obj_id` | Fastest — positional index |
| Cross-module linking | `serial_id` | Stable across compilations |
| Version compatibility check | `class_hash` | Structural mismatch detection |
| SDN text format | Name string | Human-readable |

### Serialization Annotations

Annotations control how types participate in serialization:

```simple
@serial_id(1)
struct Point:
    @serial_id(1)
    x: f64

    @serial_id(2)
    y: f64

    @skip                        # Excluded from serialization
    cached_magnitude: f64?

    @serial_id(3)
    @default(0.0)                # Default value if missing on deserialize
    z: f64
```

**Supported annotations:**

| Annotation | Target | Effect |
|------------|--------|--------|
| `@serial_id(N)` | struct, class, enum, fn, field, variant | Assigns stable numeric ID |
| `@skip` | field | Exclude from serialization entirely |
| `@skip_if_nil` | field | Skip if value is nil |
| `@default(V)` | field | Use V when missing during deserialize |
| `@rename("name")` | field | Different wire name vs code name |
| `@flatten` | field (struct type) | Inline fields into parent |
| `@transient` | field | Alias for `@skip` (Java convention) |

### Binary Serialization (`.shb`)

Position-based encoding with string table interning:

```simple
# Writer
fn shb_write(surface: ApiSurface, path: text) -> Result<(), text>:
    var writer = ShbWriter.create()
    writer.write_header(surface)
    writer.write_string_table()
    writer.write_functions(surface.functions)
    writer.write_structs(surface.structs)
    writer.write_classes(surface.classes)
    writer.write_enums(surface.enums)
    writer.write_traits(surface.traits)
    writer.write_serial_map()
    writer.finalize(path)

# Reader
fn shb_read(path: text) -> Result<ApiSurface, text>:
    val bytes = file_read_bytes(path) ?? return Err("cannot read {path}")
    var reader = ShbReader.from_bytes(bytes)
    reader.read_header()?
    reader.read_string_table()?
    val surface = ApiSurface.create(reader.module_path())
    reader.read_functions(surface)?
    reader.read_structs(surface)?
    reader.read_classes(surface)?
    reader.read_enums(surface)?
    reader.read_traits(surface)?
    Ok(surface)
```

### SDN Serialization (`.shd`)

Human-readable companion format:

```sdn
# Simple Header: math.vector
# Generated: 2026-03-01T14:32:00Z
# Interface Hash: 0xA1B2C3D4E5F60718
# Source Hash: 0x1234567890ABCDEF

module = "math.vector"
source = "src/lib/common/math/vector.spl"

[functions]

    [[fn]]
    name = "dot"
    serial_id = 1
    params = [
        { name = "a", type = "Vector" },
        { name = "b", type = "Vector" }
    ]
    return_type = "f64"
    async = false

    [[fn]]
    name = "cross"
    serial_id = 2
    params = [
        { name = "a", type = "Vector3" },
        { name = "b", type = "Vector3" }
    ]
    return_type = "Vector3"

[structs]

    [[struct]]
    name = "Vector"
    serial_id = 1
    class_hash = "0xABCD1234"
    fields = [
        { name = "x", type = "f64", serial_id = 1 },
        { name = "y", type = "f64", serial_id = 2 },
        { name = "z", type = "f64", serial_id = 3, default = "0.0" }
    ]
    methods = ["dot", "cross", "magnitude", "normalize"]
    generics = []

[traits]

    [[trait]]
    name = "Numeric"
    serial_id = 1
    required = ["add", "sub", "mul"]
    default = ["sum"]
    assoc_types = [
        { name = "Output", bound = "Self" }
    ]

[imports]
    "std.math" = ["sqrt", "atan2"]
    "std.fmt" = ["Display"]

[exports]
    "Vector" = { kind = "struct", serial_id = 1 }
    "dot" = { kind = "fn", serial_id = 1 }
    "cross" = { kind = "fn", serial_id = 2 }
    "Numeric" = { kind = "trait", serial_id = 1 }
```

---

## Header AST Extractor

### What Goes Into the Header

The header AST is a **public-only subset** of the full parsed AST. The extractor filters by visibility and strips implementation bodies.

**Included:**

| Symbol Kind | What Is Kept | What Is Stripped |
|-------------|-------------|-----------------|
| `fn` (pub) | Name, params, return type, generics, flags | Function body |
| `struct` (pub) | Name, fields (pub), generics, class_hash | Private fields |
| `class` (pub) | Name, fields (pub), method signatures, generics | Method bodies, private members |
| `enum` (pub) | Name, variants, generics | — |
| `trait` (pub) | Name, required/default method sigs, assoc types | Default method bodies |
| `type alias` (pub) | Name, target type | — |
| `val` (pub const) | Name, type, value | — |
| `export use` | Re-export path and names | — |

**Excluded:**
- Private functions, structs, classes
- Function bodies (only signatures kept)
- Internal helper functions
- Test code
- Comments and docstrings (optional: can be included with flag)

### Extraction Algorithm

```
extract_header(ast: ParsedModule) -> HeaderAst:
    header = HeaderAst.create(ast.module_path)

    for decl in ast.declarations:
        if not is_public(decl):
            continue

        match decl.kind:
            DECL_FN:
                sig = extract_function_sig(decl)
                header.add_function(sig)

            DECL_STRUCT:
                sig = extract_struct_sig(decl)
                sig.class_hash = compute_class_hash(decl)
                header.add_struct(sig)

            DECL_CLASS:
                sig = extract_class_sig(decl)
                sig.class_hash = compute_class_hash(decl)
                header.add_class(sig)

            DECL_ENUM:
                sig = extract_enum_sig(decl)
                header.add_enum(sig)

            DECL_TRAIT:
                sig = extract_trait_sig(decl)
                header.add_trait(sig)

            DECL_TYPE_ALIAS:
                header.add_type_alias(decl.name, decl.target_type)

            DECL_IMPORT:
                header.add_import(decl.module_path, decl.names)

            DECL_EXPORT:
                header.add_export(decl.names)

    header.interface_hash = hash_header(header)
    header
```

### Class Hash Computation

The `class_hash` detects structural incompatibility. Computed as FNV-1a over the canonical shape:

```
compute_class_hash(decl) -> u64:
    var hasher = fnv1a_init()
    hasher.update(decl.name)

    for field in decl.fields.sorted_by(_.serial_id):
        hasher.update(field.name)
        hasher.update(field.type_name)

    for method in decl.methods.sorted_by(_.name):
        hasher.update(method.name)
        hasher.update(method.return_type)
        for param in method.params:
            hasher.update(param.type_name)

    hasher.finalize()
```

---

## Watcher Integration

### Enhanced Watch Flow

```
┌─────────────────────────────────────────────────────────────────┐
│ Watcher Loop                                                    │
│                                                                 │
│  1. Detect changed file (poll / inotify)                        │
│  2. Parse changed file → full AST                               │
│  3. Extract header AST (public-only)                            │
│  4. Compute interface_hash                                      │
│  5. Compare with cached .shb interface_hash                     │
│     ├── SAME → Skip downstream recompilation (interface stable) │
│     └── DIFF → Write new .shb + .shd, mark dependents dirty    │
│  6. Compile changed file → SMF (always, for runtime)            │
│  7. Recompile dirty dependents (those whose dep .shb changed)   │
└─────────────────────────────────────────────────────────────────┘
```

### Integration with Incremental Compilation

The existing `IncrementalState` in `src/compiler/80.driver/incremental.spl` tracks file hashes and dependencies. The `.shb` system adds a **second-level check**:

```
Current:  source_hash changed  →  recompile file + all dependents
Proposed: source_hash changed  →  recompile file
          interface_hash changed →  recompile dependents
          interface_hash same   →  skip dependents (fast path)
```

This means internal-only changes (refactoring a function body, adding private helpers) do **not** trigger recompilation of downstream modules.

### WatchConfig Extension

```simple
struct WatchConfig:
    # ... existing fields ...
    shb_cache_dir: text?        # Directory for .shb files (nil = disabled)
    shd_companion: bool         # Also generate .shd text format
    skip_if_interface_stable: bool  # Enable interface-hash optimization
```

---

## Implementation Plan

### Phase 1: Header AST Extractor (Foundation)

**Files to create:**
- `src/compiler/90.tools/header_extractor.spl` — Extract public AST from parsed module
- `src/compiler/90.tools/header_types.spl` — HeaderAst, HeaderFunction, HeaderStruct, etc.

**Depends on:** Existing `api_surface.spl` types, `visibility.spl`

### Phase 2: SHB Binary Writer/Reader

**Files to create:**
- `src/compiler/70.backend/linker/shb_header.spl` — 64-byte header struct + constants
- `src/compiler/70.backend/linker/shb_writer.spl` — Binary serialization
- `src/compiler/70.backend/linker/shb_reader.spl` — Binary deserialization

**Depends on:** Phase 1, existing SMF byte-level patterns

### Phase 3: SDN Companion Writer/Reader

**Files to create:**
- `src/compiler/90.tools/shd_writer.spl` — SDN text serialization
- `src/compiler/90.tools/shd_reader.spl` — SDN text deserialization

**Depends on:** Phase 1, existing SDN infrastructure

### Phase 4: Serialization Annotations

**Files to modify:**
- `src/compiler/10.frontend/core/parser.spl` — Parse `@serial_id`, `@skip`, `@default`, etc.
- `src/compiler/10.frontend/core/ast.spl` — Store annotation data on AST nodes
- `src/compiler/90.tools/header_extractor.spl` — Propagate annotations to header

### Phase 5: Watcher Integration

**Files to modify:**
- `src/compiler/80.driver/build/watch.spl` — Add `.shb` generation + interface-hash comparison
- `src/compiler/80.driver/incremental.spl` — Add interface_hash to `FileHash` struct

### Phase 6: Serial ID Auto-Assignment

**Files to create:**
- `src/compiler/90.tools/serial_id_tracker.spl` — Persist and auto-assign serial IDs

**Behavior:** If `@serial_id` not specified, auto-assign next available. Store mapping in `.build/serial_ids.sdn` for stability across compilations.

---

## Comparison with Existing Formats

| Aspect | SMF | SHB (proposed) | .shd (proposed) |
|--------|-----|----------------|-----------------|
| **Purpose** | Compiled module (code+data) | Module interface (types+sigs) | Debuggable interface |
| **Contains code?** | Yes (machine code) | No (signatures only) | No |
| **Header size** | 128 bytes | 64 bytes | N/A (text) |
| **String table** | Yes (names) | Yes (names+types) | Inline |
| **Symbol table** | Yes (addresses) | Yes (signatures) | Inline |
| **Compression** | Optional (zstd/lz4) | Optional | No |
| **Human-readable** | No | No | Yes (SDN) |
| **Used for** | Execution, linking | Compilation, type checking | Debugging, diffing |

---

## Benefits

1. **Faster incremental builds** — Skip dependent recompilation when interface unchanged
2. **Decoupled interface** — Modules only need `.shb` to compile against, not full source
3. **Stable IDs** — `serial_id` enables binary format evolution without breakage
4. **Structural checks** — `class_hash` catches incompatible changes automatically
5. **Debuggable** — `.shd` companion provides human-readable view of any `.shb`
6. **Consistent with SMF** — Reuses same patterns (string table, section-based, byte-level)

## Limitations

1. **No cross-compilation metadata** — `.shb` doesn't store platform-specific info (use SMF for that)
2. **Serial ID management** — Auto-assignment requires persistent tracker file
3. **Generic bodies excluded** — Generics that need monomorphization still require source access
4. **Annotation overhead** — `@serial_id` is opt-in; without it, evolution relies on name matching

---

## Success Metrics

- [ ] Header extractor produces correct public-only API from 10+ stdlib modules
- [ ] `.shb` round-trip: write → read → compare = identical `ApiSurface`
- [ ] `.shd` round-trip: write → read → compare = identical `ApiSurface`
- [ ] Watcher skips dependent recompilation when only function body changes
- [ ] Interface-hash detects when public signature changes
- [ ] `class_hash` detects field reorder, type change, addition, removal
- [ ] `@skip` annotation excludes field from `.shb` output
- [ ] `@serial_id` annotation preserved through full pipeline

---

## References

- `src/compiler/90.tools/api_surface.spl` — Existing API surface tracking
- `src/compiler/70.backend/linker/smf_header.spl` — SMF header (pattern reference)
- `src/compiler/80.driver/incremental.spl` — Incremental compilation state
- `src/compiler/80.driver/build/watch.spl` — Build watcher
- `src/compiler/00.common/visibility.spl` — Visibility model
- `src/compiler/20.hir/inference/serialize.spl` — HIR SDN serialization
- `src/compiler/40.mono/monomorphize/metadata.spl` — Generic metadata
- `doc/design/smf_note_sdn_implementation.md` — SMF note.sdn design
- `doc/design/sdn_handler_trait_design.md` — SDN handler traits
