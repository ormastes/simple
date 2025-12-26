# Settlement and Executable Packaging

## Overview

This document describes the Settlement infrastructure for consolidating multiple SMF modules
into a single runtime container, with support for native libraries and executable packaging.

## Features

### Feature 1: Settlement Container (Core)
**Priority: High**

A runtime container that consolidates multiple SMF modules into merged memory regions.

```
Settlement
├── Header (settlement metadata)
├── CODE REGION (merged, RX protection)
├── DATA REGION (merged, RW protection)
├── INDIRECTION TABLES
│   ├── Function Table (func_ptr, module_id, version)
│   ├── Global Table (data_ptr, module_id, size)
│   └── Type Info Table (type_ptr, layout_hash)
├── MODULE REGISTRY
│   ├── ModuleEntry[] (per-module metadata)
│   ├── Code/data offsets
│   └── Dependency graph
└── NATIVE LIBS (embedded or references)
```

**API:**
```rust
pub struct Settlement {
    header: SettlementHeader,
    code_region: MemoryRegion,
    data_region: MemoryRegion,
    func_table: IndirectionTable<FuncEntry>,
    global_table: IndirectionTable<GlobalEntry>,
    type_table: IndirectionTable<TypeEntry>,
    modules: Vec<ModuleEntry>,
    native_libs: Vec<NativeLibEntry>,
}

impl Settlement {
    fn new() -> Self;
    fn add_module(&mut self, smf: &LoadedModule) -> Result<ModuleHandle>;
    fn remove_module(&mut self, handle: ModuleHandle) -> Result<()>;
    fn get_entry_point(&self) -> Option<usize>;
    fn resolve_symbol(&self, name: &str) -> Option<usize>;
    fn compact(&mut self) -> Result<()>;
}
```

### Feature 2: Extended SMF Format (Settlement SMF)
**Priority: High**

Extended SMF format that carries additional information for settlement operations.

```
Settlement SMF Layout (front-to-back for executable compatibility):
┌─────────────────────────────────────────┐
│ EXECUTABLE STUB (optional, for .exe)    │  <- Can run directly
│   - Platform-specific loader stub       │
│   - Jumps to settlement entry point     │
├─────────────────────────────────────────┤
│ SETTLEMENT HEADER                       │  <- Extended SMF header
│   - Magic: "SSMF" (Settlement SMF)      │
│   - Version, flags                      │
│   - Section offsets                     │
│   - Native lib count                    │
│   - Module count                        │
├─────────────────────────────────────────┤
│ CODE SECTION (uncompressed)             │  <- Executable code
│   - Merged code from all modules        │
│   - Native stubs for FFI                │
├─────────────────────────────────────────┤
│ DATA SECTION (uncompressed)             │  <- Runtime data
│   - Merged data from all modules        │
│   - Indirection tables                  │
├─────────────────────────────────────────┤
│ NATIVE LIBS SECTION                     │  <- Native code
│   - Statically linked libs (embedded)   │
│   - Shared lib references (paths)       │
├─────────────────────────────────────────┤
│ SYMBOL TABLE (uncompressed)             │  <- Fast lookup needed
├─────────────────────────────────────────┤
│ MODULE REGISTRY (compressed)            │  <- Module metadata
│   - Original module info                │
│   - Dependency graph                    │
│   - Version info                        │
├─────────────────────────────────────────┤
│ DEBUG INFO (compressed, optional)       │  <- Development only
├─────────────────────────────────────────┤
│ RESOURCES (compressed)                  │  <- Assets, configs
│   - Package manifest (simple.toml)      │
│   - Lock file (simple.lock)             │
│   - Other resources                     │
├─────────────────────────────────────────┤
│ ZIP DIRECTORY (for resources)           │  <- Standard zip format
└─────────────────────────────────────────┘
```

**Header Structure:**
```rust
#[repr(C)]
pub struct SettlementHeader {
    pub magic: [u8; 4],           // "SSMF"
    pub version: u16,             // Format version
    pub flags: u16,               // EXECUTABLE | RELOADABLE | HAS_NATIVES | COMPRESSED
    pub arch: u8,                 // Target architecture
    pub reserved: [u8; 3],

    // Section offsets (from start of file)
    pub code_offset: u64,
    pub code_size: u64,
    pub data_offset: u64,
    pub data_size: u64,
    pub native_offset: u64,
    pub native_size: u64,
    pub symtab_offset: u64,
    pub symtab_size: u64,
    pub registry_offset: u64,
    pub registry_size: u64,
    pub debug_offset: u64,
    pub debug_size: u64,
    pub resource_offset: u64,
    pub resource_size: u64,

    // Counts
    pub module_count: u32,
    pub native_lib_count: u32,
    pub entry_module_idx: u32,    // Which module has main()
    pub entry_func_idx: u32,      // Function table index for entry

    // Checksums
    pub code_checksum: u32,
    pub full_checksum: u32,
}

pub const SSMF_MAGIC: [u8; 4] = *b"SSMF";
pub const SSMF_FLAG_EXECUTABLE: u16 = 0x0001;
pub const SSMF_FLAG_RELOADABLE: u16 = 0x0002;
pub const SSMF_FLAG_HAS_NATIVES: u16 = 0x0004;
pub const SSMF_FLAG_COMPRESSED: u16 = 0x0008;
pub const SSMF_FLAG_DEBUG: u16 = 0x0010;
```

### Feature 3: Native Library Support
**Priority: High**

Support for embedding or referencing native libraries in SMF and Settlement.

**Native Lib Entry:**
```rust
#[repr(C)]
pub struct NativeLibEntry {
    pub name_offset: u32,         // Offset to lib name string
    pub name_len: u16,
    pub lib_type: u8,             // STATIC | SHARED | SYSTEM
    pub flags: u8,
    pub data_offset: u64,         // For STATIC: offset to embedded lib
    pub data_size: u64,           // For STATIC: size of embedded lib
    pub symbols_offset: u32,      // Offset to exported symbols list
    pub symbols_count: u32,
}

pub const NATIVE_LIB_STATIC: u8 = 0x01;   // Embedded in settlement
pub const NATIVE_LIB_SHARED: u8 = 0x02;   // Load from path
pub const NATIVE_LIB_SYSTEM: u8 = 0x03;   // System library (libc, etc.)
```

**API:**
```rust
impl Settlement {
    fn add_native_static(&mut self, name: &str, lib_data: &[u8]) -> Result<NativeHandle>;
    fn add_native_shared(&mut self, name: &str, path: &Path) -> Result<NativeHandle>;
    fn add_native_system(&mut self, name: &str) -> Result<NativeHandle>;
    fn resolve_native_symbol(&self, lib: NativeHandle, name: &str) -> Option<usize>;
}
```

### Feature 4: Startup-Only Loader (.exe)
**Priority: High**

Minimal loader for executing settlement files directly as executables.

**Design:**
```
startup_loader (embedded in .exe settlement)
├── Parse settlement header
├── Map code section (RX)
├── Map data section (RW)
├── Load native libs
│   ├── Static: already in memory
│   └── Shared: dlopen/LoadLibrary
├── Apply startup relocations (minimal)
├── Initialize indirection tables
└── Jump to entry point
```

**Implementation:**
```rust
// Minimal startup - no module management, no hot reload
pub struct StartupLoader {
    header: SettlementHeader,
    code_base: *mut u8,
    data_base: *mut u8,
    native_handles: Vec<NativeLibHandle>,
}

impl StartupLoader {
    /// Load from current executable (for embedded settlement)
    pub fn load_self() -> Result<Self>;

    /// Load from file path
    pub fn load_file(path: &Path) -> Result<Self>;

    /// Get entry point and run
    pub fn run(&self, args: &[&str]) -> i32;
}
```

**Executable Stub (platform-specific):**
```
Linux/macOS (ELF header + stub):
- Minimal ELF header pointing to stub
- Stub finds settlement header offset
- Calls StartupLoader::load_self()

Windows (PE header + stub):
- Minimal PE header pointing to stub
- Stub finds settlement header offset
- Calls StartupLoader::load_self()
```

### Feature 5: Settlement Builder
**Priority: Medium**

Tool/API for building settlement packages from multiple SMF modules.

```rust
pub struct SettlementBuilder {
    modules: Vec<PathBuf>,
    native_libs: Vec<NativeLibSpec>,
    entry_module: String,
    compress_resources: bool,
    include_debug: bool,
    target_arch: Arch,
}

impl SettlementBuilder {
    pub fn new() -> Self;
    pub fn add_module(&mut self, path: &Path) -> &mut Self;
    pub fn add_native_static(&mut self, name: &str, path: &Path) -> &mut Self;
    pub fn add_native_shared(&mut self, name: &str, path: &Path) -> &mut Self;
    pub fn set_entry(&mut self, module: &str) -> &mut Self;
    pub fn compress(&mut self, enable: bool) -> &mut Self;
    pub fn include_debug(&mut self, enable: bool) -> &mut Self;

    /// Build settlement SMF file
    pub fn build(&self, output: &Path) -> Result<()>;

    /// Build executable settlement (.exe)
    pub fn build_executable(&self, output: &Path) -> Result<()>;
}
```

### Feature 6: Slot-Based Memory Allocator
**Priority: Medium**

Efficient memory management for settlement regions.

```rust
pub struct SlotAllocator {
    base: *mut u8,
    slot_size: usize,
    total_slots: usize,
    bitmap: Vec<u64>,          // 1 = occupied, 0 = free
    free_count: usize,
}

impl SlotAllocator {
    pub fn new(region_size: usize, slot_size: usize) -> Self;
    pub fn allocate(&mut self, slots_needed: usize) -> Option<SlotRange>;
    pub fn free(&mut self, range: SlotRange);
    pub fn defragment(&mut self) -> Vec<(SlotRange, SlotRange)>; // old -> new mappings
}

// Slot sizes by region
const CODE_SLOT_SIZE: usize = 64 * 1024;   // 64KB
const DATA_SLOT_SIZE: usize = 16 * 1024;   // 16KB
const TABLE_SLOT_SIZE: usize = 4 * 1024;   // 4KB
```

### Feature 7: Indirection Tables
**Priority: Medium**

Tables for indirect function/global access enabling hot reload.

```rust
#[repr(C)]
pub struct FuncEntry {
    pub code_ptr: AtomicUsize,    // Pointer to function code
    pub module_id: u16,
    pub version: u16,
    pub flags: u32,               // VALID | TOMBSTONE | TRAMPOLINE
}

#[repr(C)]
pub struct GlobalEntry {
    pub data_ptr: AtomicUsize,
    pub size: u32,
    pub module_id: u16,
    pub flags: u16,
}

pub struct IndirectionTable<T> {
    entries: Vec<T>,
    free_list: Vec<usize>,
}

impl<T: Default> IndirectionTable<T> {
    pub fn allocate(&mut self) -> usize;
    pub fn free(&mut self, idx: usize);
    pub fn get(&self, idx: usize) -> &T;
    pub fn get_mut(&mut self, idx: usize) -> &mut T;
}
```

## File Structure

```
src/
├── loader/
│   └── src/
│       ├── settlement/           # NEW: Settlement infrastructure
│       │   ├── mod.rs
│       │   ├── container.rs      # Settlement struct
│       │   ├── builder.rs        # SettlementBuilder
│       │   ├── tables.rs         # Indirection tables
│       │   ├── slots.rs          # Slot allocator
│       │   └── native.rs         # Native lib handling
│       ├── smf/
│       │   ├── settlement.rs     # NEW: Settlement SMF format
│       │   └── ...
│       ├── startup.rs            # NEW: Startup-only loader
│       └── ...
├── linker/
│   └── src/
│       └── settlement_writer.rs  # NEW: Write settlement SMF
└── driver/
    └── src/
        └── commands/
            └── pack.rs           # NEW: `simple pack` command
```

## CLI Commands

```bash
# Build settlement from project
simple pack --output app.ssmf

# Build executable settlement
simple pack --executable --output app.exe

# Build with native libs
simple pack --native-static ./libfoo.a --output app.ssmf

# Run settlement directly
./app.exe [args]
# or
simple run app.ssmf [args]
```

## Implementation Phases

### Phase 1: Core Infrastructure
1. Settlement container struct
2. Indirection tables
3. Slot allocator
4. Basic add_module/remove_module

### Phase 2: Settlement SMF Format
1. Define header structure
2. Settlement writer (linker)
3. Settlement reader (loader)
4. Module registry serialization

### Phase 3: Native Library Support
1. NativeLibEntry structure
2. Static lib embedding
3. Shared lib loading
4. Symbol resolution across native libs

### Phase 4: Executable Packaging
1. Platform-specific stubs (ELF/PE)
2. StartupLoader implementation
3. Self-loading from executable
4. Resource compression (zip tail)

### Phase 5: Tooling
1. SettlementBuilder API
2. `simple pack` CLI command
3. Debug info support
4. Hot reload enhancements

## Compatibility

- Settlement SMF is backward compatible with regular SMF readers (they see first module)
- Regular SMF can be loaded into settlement at runtime
- Executable settlements work as standalone binaries
- Resources accessible via standard zip tools (tail of file)

## Executable Packaging Format

Settlement executables use a standard approach for self-extracting archives:
the settlement data is appended after the executable stub, with a trailer
that allows the loader to find the settlement data offset.

### Layout

```
+----------------------------------+
| Executable Stub                  |  <- Platform-specific (ELF/PE)
| (provided by user or template)   |
+----------------------------------+
| Settlement Data (SSMF format)    |  <- Settlement header + sections
|   - SSMF Header                  |
|   - String Table                 |
|   - Code Section                 |
|   - Data Section                 |
|   - Function Table               |
|   - Global Table                 |
|   - Type Table                   |
|   - Module Table                 |
|   - Native Lib Table             |
+----------------------------------+
| Trailer (16 bytes)               |
|   - 8 bytes: settlement offset   |  <- Offset where SSMF starts
|   - 8 bytes: "SSMFOFFS" magic    |  <- Trailer identifier
+----------------------------------+
```

### File Extension

- **Windows**: `.exe` - Windows recognizes and executes directly
- **Linux/macOS**: No extension or `.exe` - marked executable via chmod
- **Package with resources**: Can append additional zip data after trailer

### Loading Process

1. `StartupLoader::load_from_self()` gets current executable path
2. Read last 16 bytes to find trailer magic "SSMFOFFS"
3. If trailer found, read settlement offset from first 8 bytes
4. If no trailer, assume file IS the settlement (offset = 0)
5. Seek to settlement offset and load SSMF data
6. Memory-map code (RX) and data (RW) sections
7. Initialize indirection tables
8. Execute entry point

### Creating Executables

```rust
let builder = SettlementBuilder::with_options(
    BuildOptions::executable("/path/to/stub.exe")
);
builder.build_to_file(&settlement, "output.exe")?;
```

The builder:
1. Writes the stub executable first
2. Appends settlement data in SSMF format
3. Writes 16-byte trailer with offset and magic

## Testing Strategy

1. Unit tests for each component (slots, tables, container)
2. Integration tests for module add/remove cycles
3. E2E tests for executable packaging
4. Platform-specific tests (Linux, macOS, Windows)
5. Native lib loading tests
