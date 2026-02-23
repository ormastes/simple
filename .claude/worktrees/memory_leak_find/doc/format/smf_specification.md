# Simple Module Format (SMF) Specification

**Specification Version:** 1.1 (Planned - with Generic Template Support & Trailer-Based Header)
**Implementation Version:** 0.1 (Current - Basic format with header at offset 0)
**Date:** 2026-02-04 (Updated)
**Status:** v0.1 Active, v1.1 Planned

⚠️ **Implementation Note:** This specification documents the **planned v1.1 format**. Current implementations generate **v0.1 format** (header at offset 0, no compression/stubs). See `doc/format/smf_implementation_status.md` for detailed status.

**⭐ Planned for v1.1**: Trailer-based header design (similar to ZIP format) to enable direct execution of SMF files

## Table of Contents

1. [Overview](#overview)
2. [File Structure](#file-structure)
3. [Header Format](#header-format)
4. [Section Types](#section-types)
5. [Symbol Table](#symbol-table)
6. [Template Sections](#template-sections)
7. [Binary Encoding](#binary-encoding)
8. [Version History](#version-history)

---

## Overview

The Simple Module Format (SMF) is a binary executable and library format designed for the Simple programming language. It supports:

- **Native code execution** (JIT and AOT compiled modules)
- **Generic template storage** (v1.1+) for deferred monomorphization
- **Cross-platform compatibility** (Linux, Windows, macOS, FreeBSD, bare metal)
- **Multi-architecture support** (x86_64, aarch64, RISC-V, WebAssembly)
- **Hot reloading** for development
- **Debug information** preservation
- **Startup optimization hints** (app type, prefetching, locality)

### Design Goals

- **Compact**: Minimal overhead compared to native formats
- **Fast Loading**: Optimized for quick startup
- **Self-Contained**: All dependencies embedded or referenced
- **Extensible**: New section types can be added without breaking compatibility
- **Generic-Aware**: Store templates for library-style generic imports (v1.1+)

---

## File Structure

### Layout Overview

⚠️ **Version Note:**
- **v0.1 (Current)**: Header at offset 0, sections follow sequentially
- **v1.1 (Planned)**: Trailer-based design with header at EOF-128

### v1.1 Layout (Trailer-Based Design - PLANNED)

An SMF v1.1 file uses a **ZIP-style trailer** where the header is located at the **end of the file** (similar to ZIP's central directory). This design enables **direct execution** by allowing an executable stub or shebang at the beginning.

```
┌──────────────────────────────────────┐ ← File Start (Offset 0)
│   [Optional Executable Stub]         │  ⭐ NEW: Enables chmod +x ./file.smf
│   #!/usr/bin/env simple              │       and direct execution
│   [ELF/PE/Mach-O stub with SMF]      │
├──────────────────────────────────────┤
│        Section Data                  │
│  - Code Section                      │
│  - Data Section                      │
│  - TemplateCode Section (v1.1+)      │
│  - TemplateMeta Section (v1.1+)      │
│  - [Other Sections]                  │
├──────────────────────────────────────┤
│        Section Table                 │
│  (64 bytes × section_count)          │
├──────────────────────────────────────┤
│        Symbol Table                  │
│  (72 bytes × symbol_count)           │
├──────────────────────────────────────┤
│        String Table                  │
│  (null-terminated symbol names)      │
├──────────────────────────────────────┤
│     SMF Header (Trailer)             │  ⭐ Located at EOF-128
│          (128 bytes)                 │     Like ZIP central directory
└──────────────────────────────────────┘ ← File End

To read an SMF file:
1. Seek to EOF - 128 bytes
2. Read SMF Header (128 bytes)
3. Validate magic number "SMF\0"
4. Use offsets from header to locate sections
```

### Why Trailer-Based Design?

**Benefits:**
- **Direct Execution**: Prepend `#!/usr/bin/env simple` for script-like usage
- **Native Embedding**: Embed SMF in ELF/PE/Mach-O executables (append to native binary)
- **Streaming Friendly**: Can write sections sequentially, header last
- **Self-Extracting**: Add extraction stub at beginning for installers

**Similar to ZIP Format:**
- ZIP stores central directory at end of file
- Allows for self-extracting archives (stub + ZIP data)
- SMF adopts same pattern for same benefits

---

### v0.1 Layout (Current Implementation)

The current v0.1 format uses a traditional layout with the header at the beginning:

```
┌──────────────────────────────────────┐ ← File Start (Offset 0)
│     SMF Header (128 bytes)           │  Header at start (traditional)
├──────────────────────────────────────┤
│        Section Table                 │  Offset specified in header
│  (64 bytes × section_count)          │
├──────────────────────────────────────┤
│        Section Data                  │
│  - Code Section                      │
│  - Data Section                      │
│  - [Other Sections]                  │
├──────────────────────────────────────┤
│        Symbol Table                  │  Offset specified in header
│  (72 bytes × symbol_count)           │
├──────────────────────────────────────┤
│        String Table                  │  Null-terminated symbol names
│  (variable length)                   │
└──────────────────────────────────────┘ ← File End
```

**To read a v0.1 SMF file:**
1. Read SMF Header from offset 0 (128 bytes)
2. Validate magic number "SMF\0"
3. Check version (major=0, minor=1)
4. Use offsets from header to locate sections and symbols

**v0.1 Limitations:**
- No executable stub support
- No compression
- No prefetch hints
- Header must be at offset 0 (cannot append to other files)

**Migration Path:**
- v1.1 loaders will try EOF-128 first, fall back to offset 0 for v0.1 files
- v0.1 files remain valid and loadable by v1.1 loaders
- No need to rewrite existing v0.1 files

---

### Pure SMF vs Executable SMF (v1.1 Only)

| Type | Structure | Use Case |
|------|-----------|----------|
| **Pure SMF** | Just SMF data + trailer | Libraries, modules loaded by Simple runtime |
| **Executable SMF** | Stub + SMF data + trailer | Scripts with `chmod +x`, self-contained apps |

**Example Executable SMF:**
```bash
#!/usr/bin/env simple
# This file is both a shell script and an SMF module!
# ... SMF binary data ...
# ... SMF header at EOF-128 ...
```

### Alignment Requirements

- **Header Trailer**: Located at EOF - 128 bytes (no alignment requirement)
- **Section Table**: Offset specified in header, 8-byte aligned
- **Sections**: Aligned to `section.alignment` (typically 16 bytes)
- **Symbol Table**: 8-byte aligned
- **String Table**: No alignment requirement

### Loader Algorithm

```rust
fn load_smf(file: &mut File) -> Result<SmfModule> {
    // 1. Read header from tail
    let file_size = file.metadata()?.len();
    file.seek(SeekFrom::Start(file_size - 128))?;
    let header = SmfHeader::read(file)?;

    // 2. Validate magic
    if &header.magic != b"SMF\0" {
        return Err(Error::InvalidMagic);
    }

    // 3. Read sections using offsets from header
    file.seek(SeekFrom::Start(header.section_table_offset))?;
    let sections = read_section_table(file, header.section_count)?;

    // 4. Load section data, symbols, etc.
    // ...
}
```

---

## Header Format

### SmfHeader Structure (128 bytes)

**⭐ Location**: EOF - 128 bytes (trailer, not at offset 0)

```rust
#[repr(C)]
pub struct SmfHeader {
    // Identification (8 bytes)
    pub magic: [u8; 4],           // "SMF\0" (0x53 0x4D 0x46 0x00)
    pub version_major: u8,        // Major version (1)
    pub version_minor: u8,        // Minor version (0=base, 1=templates+trailer)
    pub platform: u8,             // Platform enum (see Platform)
    pub arch: u8,                 // Architecture enum (see Arch)

    // Flags and counts (20 bytes)
    pub flags: u32,               // Module flags (see SMF_FLAG_*)
    pub compression: u8,          // ⭐ NEW: Compression type (0=none, 1=zstd, 2=lz4)
    pub compression_level: u8,    // ⭐ NEW: Compression level (0-22 for zstd, 0=default)
    pub reserved_compression: [u8; 2], // ⭐ NEW: Reserved for future compression options
    pub section_count: u32,       // Number of sections
    pub section_table_offset: u64, // Offset to section table

    // Symbol table (16 bytes)
    pub symbol_table_offset: u64, // Offset to symbol table
    pub symbol_count: u32,        // Total number of symbols
    pub exported_count: u32,      // Number of exported symbols

    // Execution (16 bytes)
    pub entry_point: u64,         // RVA of entry point (0 if library)
    pub stub_size: u32,           // ⭐ NEW: Size of executable stub (0 if pure SMF)
    pub smf_data_offset: u32,     // ⭐ NEW: Offset where SMF data begins (after stub)

    // Hashing (16 bytes)
    pub module_hash: u64,         // Hash of module contents (excludes stub)
    pub source_hash: u64,         // Hash of source code

    // Startup optimization hints (12 bytes)
    pub app_type: u8,             // Application type (0=cli, 1=tui, 2=gui, 3=service, 4=repl)
    pub window_width: u16,        // Window width hint (GUI apps)
    pub window_height: u16,       // Window height hint (GUI apps)
    pub prefetch_hint: u8,        // Prefetch hint (0=no, 1=yes)
    pub prefetch_file_count: u8,  // Expected file count for prefetch
    pub reserved: [u8; 5],        // Reserved for future use (was [u8; 1])

    // Total: 128 bytes
}
```

### Reading the Header (Trailer)

```rust
/// Read SMF header from tail of file
fn read_smf_header(file: &mut File) -> Result<SmfHeader> {
    let file_size = file.metadata()?.len();

    // SMF header is always at EOF - 128 bytes
    file.seek(SeekFrom::Start(file_size - 128))?;

    let mut header_bytes = [0u8; 128];
    file.read_exact(&mut header_bytes)?;

    let header: SmfHeader = unsafe { std::mem::transmute(header_bytes) };

    // Validate magic
    if &header.magic != b"SMF\0" {
        return Err(Error::InvalidMagic);
    }

    Ok(header)
}
```

### Header Fields

#### Magic Number
- **Value**: `"SMF\0"` (0x53 0x4D 0x46 0x00)
- **Purpose**: File type identification
- **Validation**: Loaders MUST reject files with incorrect magic

#### Version
- **Major**: Breaking changes (current: 1)
- **Minor**: Backward-compatible additions
  - `0`: Base format
  - `1`: Generic template support added
- **Compatibility**: Loaders MAY reject unsupported versions

#### Platform Enum

| Value | Platform | Description |
|-------|----------|-------------|
| 0 | Any | Platform-independent bytecode |
| 1 | Linux | Linux systems |
| 2 | Windows | Windows systems |
| 3 | MacOS | macOS systems |
| 4 | FreeBSD | FreeBSD systems |
| 5 | None | Bare metal / no OS |

#### Architecture Enum

| Value | Architecture | Bits | Description |
|-------|--------------|------|-------------|
| 0 | X86_64 | 64 | x86-64 / AMD64 |
| 1 | Aarch64 | 64 | ARM 64-bit |
| 2 | X86 | 32 | x86 32-bit |
| 3 | Arm | 32 | ARM 32-bit |
| 4 | Riscv64 | 64 | RISC-V 64-bit |
| 5 | Riscv32 | 32 | RISC-V 32-bit |
| 6 | Wasm32 | 32 | WebAssembly 32-bit |
| 7 | Wasm64 | 64 | WebAssembly 64-bit |

#### Compression Field ⭐ NEW

Specifies compression algorithm used for section data.

| Value | Algorithm | Description |
|-------|-----------|-------------|
| 0 | **None** | No compression (default) ⭐ |
| 1 | Zstd | Zstandard compression (high ratio) |
| 2 | Lz4 | LZ4 compression (high speed) |
| 3-255 | Reserved | Reserved for future algorithms |

**Default**: 0 (no compression) - enables direct code execution without decompression overhead.

**Compression Level**:
- **0**: Default level for the algorithm
- **1-22**: Zstd compression levels (higher = better compression, slower)
- **1-12**: LZ4 compression levels (LZ4HC mode)
- Level only applies when compression != 0

**Per-Section Compression**:
- If `compression == 0`: All sections uncompressed
- If `compression != 0`: Sections MAY be individually compressed
  - Check `SmfSection.flags` bit 4 (`SECTION_FLAG_COMPRESSED`)
  - Unset = section stored uncompressed
  - Set = section compressed using header's compression algorithm

#### Stub Fields ⭐ NEW

Enable executable SMF files with prepended stubs.

**stub_size**: Size in bytes of executable stub at file beginning
- **0**: Pure SMF file (no stub)
- **> 0**: Executable SMF with stub

**smf_data_offset**: Where SMF sections begin (after stub)
- **Pure SMF**: `smf_data_offset == 0`
- **Executable SMF**: `smf_data_offset == stub_size`

**Example Executable SMF**:
```
File structure:
[Shebang stub: 64 bytes] <- stub_size = 64
[SMF sections...]        <- smf_data_offset = 64
[SMF header @ EOF-128]   <- stub_size = 64, smf_data_offset = 64
```

#### Flags Bitmask

| Bit | Name | Description |
|-----|------|-------------|
| 0 | `SMF_FLAG_EXECUTABLE` | Module is executable (has entry point) |
| 1 | `SMF_FLAG_RELOADABLE` | Module supports hot reloading |
| 2 | `SMF_FLAG_DEBUG_INFO` | Debug information included |
| 3 | `SMF_FLAG_PIC` | Position-independent code |
| 4 | `SMF_FLAG_HAS_STUB` | ⭐ NEW: File has executable stub |
| 5-31 | Reserved | Reserved for future use |

**Note**: Removed old `SMF_FLAG_COMPRESSED` (bit 4) - use `compression` field instead

#### Application Type

| Value | Type | Optimizations |
|-------|------|---------------|
| 0 | CLI | Minimal resources, fast startup |
| 1 | TUI | Terminal buffers, keyboard input |
| 2 | GUI | Window creation, GPU context |
| 3 | Service | IPC, signal handlers, background |
| 4 | REPL | History, line editor, interactive |

---

## Section Types

### SmfSection Structure (64 bytes)

```rust
#[repr(C)]
pub struct SmfSection {
    pub section_type: SectionType, // u8: Section type enum
    // 3 bytes padding
    pub flags: u32,                 // Section flags (READ/WRITE/EXEC)
    pub offset: u64,                // File offset to section data
    pub size: u64,                  // Size of section data in file
    pub virtual_size: u64,          // Size in memory (may differ for BSS)
    pub alignment: u64,             // Required alignment (power of 2)
    pub name: [u8; 16],             // Section name (null-terminated)
}
```

### Section Type Enum

| Value | Type | Description |
|-------|------|-------------|
| 1 | Code | Executable machine code |
| 2 | Data | Initialized writable data |
| 3 | RoData | Read-only data (constants, strings) |
| 4 | Bss | Uninitialized data (zero-filled) |
| 5 | Reloc | Relocation entries |
| 6 | SymTab | Symbol table |
| 7 | StrTab | String table |
| 8 | Debug | Debug information (DWARF, etc.) |
| 9 | TypeInfo | Type metadata |
| 10 | Version | Version information |
| 11 | SrcMap | Source code mapping |
| **12** | **TemplateCode** | **Generic templates (AST/MIR)** ⭐ NEW |
| **13** | **TemplateMeta** | **Monomorphization metadata** ⭐ NEW |

### Section Flags

| Bit | Name | Description |
|-----|------|-------------|
| 0 | `SECTION_FLAG_READ` | Section is readable |
| 1 | `SECTION_FLAG_WRITE` | Section is writable |
| 2 | `SECTION_FLAG_EXEC` | Section is executable |
| 3 | `SECTION_FLAG_COMPRESSED` | ⭐ NEW: Section data is compressed |
| 4-31 | Reserved | Reserved for future use |

**Compression Note**:
- If `SmfHeader.compression == 0`: Bit 3 ignored, all sections uncompressed
- If `SmfHeader.compression != 0`: Bit 3 indicates per-section compression
  - Unset: Section stored uncompressed (for code that needs direct execution)
  - Set: Section compressed using algorithm from `SmfHeader.compression`

### Standard Sections

#### Code Section
- **Type**: 1 (Code)
- **Flags**: `READ | EXEC` (0x05)
- **Content**: Native machine code or bytecode
- **Alignment**: 16 bytes (recommended)

#### Data Section
- **Type**: 2 (Data)
- **Flags**: `READ | WRITE` (0x03)
- **Content**: Initialized mutable data
- **Alignment**: 8 bytes

#### RoData Section
- **Type**: 3 (RoData)
- **Flags**: `READ` (0x01)
- **Content**: Constants, string literals
- **Alignment**: 8 bytes

---

## Symbol Table

### SmfSymbol Structure (72 bytes)

```rust
#[repr(C)]
pub struct SmfSymbol {
    // Identification (8 bytes)
    pub name_offset: u32,         // Offset into string table
    pub name_hash: u32,           // FNV-1a hash of name

    // Type and binding (4 bytes)
    pub sym_type: SymbolType,     // u8: Symbol type enum
    pub binding: SymbolBinding,   // u8: Local/Global/Weak
    pub visibility: u8,           // Visibility (0=default)
    pub flags: u8,                // Symbol flags (see below)

    // Location and size (16 bytes)
    pub value: u64,               // Symbol value (RVA or absolute)
    pub size: u64,                // Symbol size in bytes

    // Metadata (8 bytes)
    pub type_id: u32,             // Type system ID
    pub version: u32,             // Symbol version

    // Generic template metadata (12 bytes) ⭐ NEW in v1.1
    pub template_param_count: u8, // Number of type parameters (0 if not generic)
    pub reserved: [u8; 3],        // Reserved for alignment
    pub template_offset: u64,     // Offset to template in TemplateCode section

    // Total: 72 bytes
}
```

### Symbol Type Enum

| Value | Type | Description |
|-------|------|-------------|
| 0 | None | Undefined symbol |
| 1 | Function | Function or method |
| 2 | Data | Global variable or constant |
| 3 | Type | Type definition (struct, enum, class) |
| 4 | Trait | Trait definition |
| 5 | Actor | Actor definition |
| 6 | Constant | Compile-time constant |

### Symbol Binding

| Value | Binding | Description |
|-------|---------|-------------|
| 0 | Local | Local to module (not exported) |
| 1 | Global | Exported, visible to other modules |
| 2 | Weak | Weak symbol (can be overridden) |

### Symbol Flags ⭐ UPDATED in v1.1

| Bits | Name | Description |
|------|------|-------------|
| 0-1 | Layout Phase | 0=startup, 1=first_frame, 2=steady, 3=cold |
| 2 | Event Loop Anchor | Symbol is event loop anchor |
| 3 | Layout Pinned | Should not be moved by optimizer |
| **4** | **Generic Template** | **Symbol is a generic template** ⭐ NEW |
| **5** | **Specialized** | **Symbol is a specialization** ⭐ NEW |
| 6-7 | Reserved | Reserved for future use |

### Symbol Flag Constants

```rust
pub mod symbol_flags {
    pub const LAYOUT_PHASE_MASK: u8 = 0x03;
    pub const EVENT_LOOP_ANCHOR: u8 = 0x04;
    pub const LAYOUT_PINNED: u8 = 0x08;
    pub const GENERIC_TEMPLATE: u8 = 0x10;  // ⭐ NEW
    pub const SPECIALIZED: u8 = 0x20;       // ⭐ NEW
}
```

### Symbol Name Hashing

Symbols are hashed using **FNV-1a** for O(1) lookup:

```rust
pub fn hash_name(name: &str) -> u32 {
    const FNV_OFFSET: u32 = 2166136261;
    const FNV_PRIME: u32 = 16777619;

    let mut hash = FNV_OFFSET;
    for byte in name.bytes() {
        hash ^= byte as u32;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}
```

---

## Template Sections ⭐ NEW in v1.1

### Overview

Template sections enable **deferred monomorphization** - storing generic definitions for later instantiation. This allows library modules to export generic functions/types that can be specialized by downstream code with new type combinations.

### TemplateCode Section (Type 12)

**Purpose**: Store serialized generic definitions (AST/MIR)

**Binary Format**:
```
┌─────────────────────────────────────┐
│ Header (10 bytes)                   │
│  - magic: "GTPL" (u32)             │
│  - version: 1 (u16)                │
│  - template_count: u32              │
├─────────────────────────────────────┤
│ Template Entries (variable)         │
│  For each template:                 │
│    - kind: u8                       │
│      (0=Function, 1=Struct,         │
│       2=Class, 3=Enum, 4=Trait)     │
│    - [Serialized AST node]          │
└─────────────────────────────────────┘
```

**Magic Number**: `"GTPL"` (0x47 0x54 0x50 0x4C) = "Generic TeMPLates"

**Template Kinds**:
| Value | Kind | Stored Data |
|-------|------|-------------|
| 0 | Function | FunctionDef AST node |
| 1 | Struct | StructDef AST node |
| 2 | Class | ClassDef AST node |
| 3 | Enum | EnumDef AST node |
| 4 | Trait | TraitDef AST node |

**Serialization Format** (per template):
```
- kind: u8
- name_len: u32
- name: [u8; name_len]
- generic_param_count: u8
- generic_params: [GenericParam; generic_param_count]
- [Type-specific fields...]
```

**Example**:
```rust
// Source: fn identity<T>(x: T) -> T { x }

// TemplateCode entry:
kind: 0 (Function)
name_len: 8
name: "identity"
generic_param_count: 1
generic_params: ["T"]
params: [Param { name: "x", type: TypeVar("T") }]
return_type: TypeVar("T")
body: [Serialized MIR]
```

### TemplateMeta Section (Type 13)

**Purpose**: Track specializations and type bindings

**Binary Format**:
```
┌─────────────────────────────────────┐
│ Header (14 bytes)                   │
│  - magic: "META" (u32)             │
│  - version: 1 (u16)                │
│  - function_count: u32              │
│  - struct_count: u32                │
│  - enum_count: u32                  │
│  - trait_count: u32                 │
├─────────────────────────────────────┤
│ Metadata Entries (variable)         │
│  [Serialized metadata]              │
└─────────────────────────────────────┘
```

**Magic Number**: `"META"` (0x4D 0x45 0x54 0x41) = "METAdata"

**Metadata Structure**:
```rust
pub struct MonomorphizationMetadata {
    pub functions: HashMap<String, GenericFunctionMeta>,
    pub structs: HashMap<String, GenericStructMeta>,
    pub enums: HashMap<String, GenericEnumMeta>,
    pub traits: HashMap<String, GenericTraitMeta>,
}

pub struct GenericFunctionMeta {
    pub base_name: String,
    pub generic_params: Vec<String>,
    pub specializations: Vec<SpecializationEntry>,
}

pub struct SpecializationEntry {
    pub type_args: Vec<ConcreteType>,
    pub mangled_name: String,
    pub bindings: HashMap<String, TypeId>,
}
```

**Purpose**:
- Track which specializations already exist in the module
- Avoid duplicate specialization generation
- Enable fast lookup of existing specializations

### Template-Aware Symbol Table

Symbols referencing generic templates have additional fields:

- **`template_param_count`**: Number of type parameters (e.g., 2 for `Pair<T, U>`)
- **`template_offset`**: Byte offset into TemplateCode section
- **`flags & GENERIC_TEMPLATE`**: Set if symbol is a template
- **`flags & SPECIALIZED`**: Set if symbol is a specialization

**Example**:

```rust
// Generic template: fn identity<T>(x: T) -> T
SmfSymbol {
    name_offset: 0,
    name_hash: hash_name("identity"),
    sym_type: SymbolType::Function,
    binding: SymbolBinding::Global,
    flags: symbol_flags::GENERIC_TEMPLATE,  // 0x10
    template_param_count: 1,
    template_offset: 42,  // Offset in TemplateCode section
    ...
}

// Specialized instance: identity$Int
SmfSymbol {
    name_offset: 10,
    name_hash: hash_name("identity$Int"),
    sym_type: SymbolType::Function,
    binding: SymbolBinding::Global,
    flags: symbol_flags::SPECIALIZED,  // 0x20
    template_param_count: 0,
    template_offset: 0,
    value: 0x1000,  // RVA of specialized code
    size: 128,      // Code size
    ...
}
```

### Usage Example

**Library** (`collections.smf`):
```simple
// Generic template (stored in TemplateCode)
struct List<T>:
    data: [T]
    fn append(item: T): ...

// Specialized instance (native code in Code section)
val my_list = List<Int>()
```

**Downstream** (`app.spl`):
```simple
import collections.List

// This works even though library didn't compile List<Float>!
val floats = List<Float>()
```

**Deferred Monomorphization Workflow**:
1. Linker/loader detects use of `List<Float>`
2. Checks TemplateMeta - not found
3. Loads `List<T>` template from TemplateCode section
4. Instantiates `List$Float` by substituting `T → Float`
5. Compiles specialized code
6. Links into final binary

---

## Binary Encoding

### Endianness
- **All multi-byte integers**: Little-endian
- **Rationale**: x86_64 and aarch64 are little-endian

### Alignment
- **Structures**: Align to largest field (typically 8 bytes)
- **Sections**: Align to `section.alignment` (typically 16 bytes)
- **Padding**: Zero-filled

### String Encoding
- **Format**: Null-terminated UTF-8
- **Location**: String table (referenced by offset)
- **Hashing**: FNV-1a for symbol lookups

---

## Version History

### Version 1.1 (2026-01-28) - Generic Template Support ⭐ CURRENT

**Added**:
- ✅ `SectionType::TemplateCode` (12) - Generic template storage
- ✅ `SectionType::TemplateMeta` (13) - Monomorphization metadata
- ✅ Symbol flags: `GENERIC_TEMPLATE` (0x10), `SPECIALIZED` (0x20)
- ✅ Symbol fields: `template_param_count`, `template_offset`
- ✅ Template serialization format (GTPL magic)
- ✅ Metadata serialization format (META magic)

**Features**:
- Deferred monomorphization (link-time and JIT-time)
- Library-style generic imports
- Template caching and specialization tracking
- Backward compatibility (modules without templates still work)

**Migration**:
- **Old loaders**: Can load v1.1 files but ignore template sections
- **New loaders**: Can load v1.0 files (no templates available)

### Version 1.0 (2025-12-01) - Base Format

**Initial Features**:
- SMF header with platform/arch detection
- Section types: Code, Data, RoData, Bss, Debug, TypeInfo, etc.
- Symbol table with FNV-1a hashing
- Startup optimization hints (app_type, prefetch)
- 4KB page locality optimization (layout phases)
- Hot reloading support

---

## Implementation References

### Rust Loader

**Location**: `src/rust/loader/src/smf/`

**Key Files**:
- `header.rs`: SmfHeader parsing and validation
- `section.rs`: Section type definitions
- `symbol.rs`: Symbol table and hashing
- `settlement.rs`: Module loading and linking

### Rust Compiler

**Location**: `src/rust/compiler/src/`

**Key Files**:
- `smf_writer.rs`: SMF generation with template support
- `monomorphize/partition.rs`: Template/specialized separation
- `monomorphize/metadata.rs`: Metadata tracking
- `monomorphize/deferred.rs`: On-demand instantiation

### Simple Compiler

**Location**: `simple/compiler/`

**Key Files**:
- `smf_writer.spl`: SMF generation (Simple implementation)
- `monomorphize/partition.spl`: Partitioning logic
- `monomorphize/deferred.spl`: Deferred monomorphizer

---

## Examples

### Minimal Executable SMF

```
Offset  | Content
--------|--------------------------------------------------
0x0000  | "SMF\0" (magic)
0x0004  | 0x01 0x00 (version 1.0)
0x0006  | 0x01 0x00 (Linux, x86_64)
0x0008  | 0x01 0x00 0x00 0x00 (flags: EXECUTABLE)
0x000C  | 0x01 0x00 0x00 0x00 (section_count: 1)
0x0010  | 0x80 0x00 0x00 0x00 0x00 0x00 0x00 0x00 (section_table_offset: 128)
...     | [Rest of header]
0x0080  | [Section table entry for Code section]
0x00C0  | [Native code]
0x0200  | [Symbol table]
0x0250  | [String table: "main\0"]
```

### SMF with Generic Templates

```
Offset  | Content
--------|--------------------------------------------------
0x0000  | "SMF\0" (magic)
0x0004  | 0x01 0x01 (version 1.1) ⭐ Minor version = 1
0x0006  | 0x01 0x00 (Linux, x86_64)
...     | [Header continues]
0x0080  | [Section table]
        |   - Code section
        |   - TemplateCode section ⭐
        |   - TemplateMeta section ⭐
0x0140  | [Native code for specialized instances]
0x0400  | [TemplateCode section]
        |   "GTPL" magic
        |   version: 1
        |   template_count: 1
        |   kind: 0 (Function)
        |   name: "identity"
        |   generic_params: ["T"]
        |   [Serialized MIR]
0x0600  | [TemplateMeta section]
        |   "META" magic
        |   version: 1
        |   function_count: 1
        |   [Metadata entries]
0x0800  | [Symbol table]
        |   Symbol: "identity" (GENERIC_TEMPLATE flag set)
        |   Symbol: "identity$Int" (SPECIALIZED flag set)
0x0900  | [String table]
```

---

## Creating Executable SMF Files ⭐ NEW

The trailer-based header design enables **directly executable SMF files** by allowing an executable stub at the beginning of the file.

### Use Cases

| Type | Description | Example |
|------|-------------|---------|
| **Script Mode** | Shebang + SMF data | `#!/usr/bin/env simple` |
| **Self-Contained** | Native stub + SMF data | Single-file application |
| **Self-Extracting** | Extraction stub + SMF | Installer that unpacks itself |
| **Hybrid Binary** | ELF/PE/Mach-O + SMF | Native binary with embedded SMF module |

### Script Mode (Shebang)

**Most Common**: Treat SMF files like shell scripts.

```bash
#!/usr/bin/env simple
# Rest of file is SMF binary data
# ... sections ...
# ... header at EOF-128 ...
```

**Create script-mode SMF:**
```bash
# 1. Compile to pure SMF
simple compile script.spl -o script.smf

# 2. Prepend shebang
echo '#!/usr/bin/env simple' | cat - script.smf > script
chmod +x script

# 3. Run directly
./script
```

**SMF Header Fields:**
```rust
SmfHeader {
    stub_size: 21,           // Length of shebang line
    smf_data_offset: 21,     // SMF sections start at offset 21
    flags: SMF_FLAG_EXECUTABLE | SMF_FLAG_HAS_STUB,
    // ...
}
```

### Self-Contained Application

**Use Case**: Single-file deployment without external runtime dependency.

```
File structure:
┌────────────────────────┐
│ Native loader stub     │  Tiny ELF/PE that loads SMF from self
│ (links libsimple.so)   │  Handles SMF parsing and execution
├────────────────────────┤
│ SMF sections           │  Application code and data
├────────────────────────┤
│ SMF header (trailer)   │
└────────────────────────┘
```

**Create self-contained app:**
```bash
# Compiler embeds loader stub automatically
simple compile --self-contained app.spl -o app
chmod +x app
./app
```

**SMF Header Fields:**
```rust
SmfHeader {
    stub_size: 4096,         // Size of native loader stub
    smf_data_offset: 4096,   // SMF data starts after stub
    flags: SMF_FLAG_EXECUTABLE | SMF_FLAG_HAS_STUB,
    // ...
}
```

### Hybrid Binary (Append SMF to Native Binary)

**Use Case**: Add SMF modules to existing native executables.

```bash
# Compile native binary
gcc main.c -o myapp

# Compile SMF module
simple compile plugin.spl -o plugin.smf

# Append SMF to binary
cat plugin.smf >> myapp

# Binary still runs normally, can discover SMF at end
./myapp
```

**Native binary can discover SMF:**
```c
int main(int argc, char** argv) {
    // Run normal logic
    run_application();

    // Check for embedded SMF
    if (has_smf_trailer(argv[0])) {
        load_and_run_smf_plugin(argv[0]);
    }
}
```

### Loader Implementation for Executable SMF

```rust
fn load_executable_smf(path: &Path) -> Result<SmfModule> {
    let mut file = File::open(path)?;
    let file_size = file.metadata()?.len();

    // 1. Read header from trailer
    file.seek(SeekFrom::Start(file_size - 128))?;
    let header = SmfHeader::read(&mut file)?;

    // 2. Check for stub
    if header.flags & SMF_FLAG_HAS_STUB != 0 {
        // Adjust all offsets by stub size
        let stub_offset = header.smf_data_offset as u64;

        // 3. Read sections from after stub
        file.seek(SeekFrom::Start(stub_offset + header.section_table_offset))?;
        // ... load sections ...
    } else {
        // Pure SMF file, no offset adjustment needed
        file.seek(SeekFrom::Start(header.section_table_offset))?;
        // ... load sections ...
    }

    Ok(module)
}
```

### File Size Examples

| Type | Size Breakdown |
|------|----------------|
| **Pure SMF** | Sections (1000) + Header (128) = **1128 bytes** |
| **Script Mode** | Shebang (21) + Sections (1000) + Header (128) = **1149 bytes** |
| **Self-Contained** | Stub (4096) + Sections (1000) + Header (128) = **5224 bytes** |
| **Hybrid** | Native (10000) + SMF (1128) = **11128 bytes** |

### Compression for Executable SMF

**Recommendation**: Default compression = 0 (no compression) for executable SMF.

**Why?**
- Code sections need direct execution (can't decompress in-place)
- Shebang/stub execution expects uncompressed code
- Faster startup (no decompression overhead)

**When to use compression:**
- Large data sections (not code)
- Library SMF files (loaded by runtime, not executed directly)
- Set `SECTION_FLAG_COMPRESSED` on individual data sections only

**Example: Compress only data sections**
```rust
SmfHeader {
    compression: 1,          // Zstd available
    compression_level: 3,    // Default level
    // ...
}

// Code section - NOT compressed (needs direct exec)
SmfSection {
    section_type: Code,
    flags: READ | EXEC,      // No COMPRESSED flag
    // ...
}

// Data section - compressed (saves space)
SmfSection {
    section_type: Data,
    flags: READ | WRITE | COMPRESSED,  // Compressed
    // ...
}
```

### Tools Support

```bash
# Create executable SMF
simple build --executable script.spl -o script
chmod +x script
./script

# Inspect executable SMF
simple inspect script
# Output:
# Type: Executable SMF
# Stub: 21 bytes (shebang)
# Sections: 5 (1000 bytes)
# Compression: None
# Entry point: 0x000100

# Extract SMF from hybrid binary
simple extract-smf hybrid_app -o extracted.smf

# Remove stub, convert to pure SMF
simple strip-stub script -o pure.smf
```

---

## Compatibility Notes

### Forward Compatibility

- **New section types**: Old loaders ignore unknown sections
- **New flags**: Old loaders ignore unknown flags
- **Reserved fields**: Must be zero for forward compatibility

### Backward Compatibility

- **v1.1 loaders**: Can load v1.0 files (no templates available)
- **v1.0 loaders**: Can load v1.1 files (ignore template sections)
- **Template-aware code**: Must check version_minor >= 1

### Validation Checklist

Loaders SHOULD validate:
- ✅ Magic number is "SMF\0"
- ✅ Version is supported
- ✅ Platform and architecture match
- ✅ Section offsets are within file bounds
- ✅ Symbol offsets are within string table bounds
- ✅ Template section magic numbers (if present)

---

## See Also

- **Design Document**: `doc/design/generic_template_bytecode.md`
- **Architecture Guide**: `doc/guide/compiler_architecture.md`
- **Feature Specification**: `test/lib/std/features/generic_bytecode_spec.spl`

---

**Authors**: Simple Language Team
**License**: MIT
**Last Updated**: 2026-01-28
