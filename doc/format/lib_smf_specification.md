# Library SMF Specification

**Version:** 1.0
**Date:** 2026-02-09
**Status:** Initial Implementation

## Overview

Library SMF (.lsm) is a container format that bundles multiple SMF (Simple Module Format) files into a single archive with a location index for fast random access. This format enables:

- **Single-file library deployment** - Distribute multiple modules as one file
- **Fast module lookup** - O(1) access via indexed location table
- **Reduced filesystem overhead** - Fewer files to manage
- **Atomic library updates** - Replace entire library in one operation

## Use Cases

| Use Case | Description |
|----------|-------------|
| **Standard Library Distribution** | Bundle `std/*` modules into `libstd.lsm` |
| **Third-Party Libraries** | Package libraries for easy distribution |
| **System Libraries** | Pre-installed libraries in `/usr/lib/simple/` |
| **Application Bundles** | Package app modules together |

## File Format

### Layout

```
┌────────────────────────────────┐ Offset 0
│  Library SMF Header            │ 128 bytes
│  - Magic: "LSMF"               │
│  - Version: 1.0                │
│  - Module count                │
│  - Index metadata              │
├────────────────────────────────┤ Offset 128
│  Module Index Table            │ 128 bytes × module_count
│  - Array of ModuleIndexEntry   │
│  - Each: name, offset, size    │
├────────────────────────────────┤ Offset 128 + (128 × count)
│  Module 1 SMF Data             │ Complete SMF file
├────────────────────────────────┤
│  Module 2 SMF Data             │ Complete SMF file
├────────────────────────────────┤
│  ...                           │
├────────────────────────────────┤
│  Module N SMF Data             │ Complete SMF file
└────────────────────────────────┘
```

### Library SMF Header (128 bytes)

```rust
struct LibSmfHeader {
    // Identification (8 bytes)
    magic: [u8; 4],           // "LSMF" (0x4C 0x53 0x4D 0x46)
    version_major: u8,        // Major version (1)
    version_minor: u8,        // Minor version (0)
    reserved1: [u8; 2],       // Reserved

    // Metadata (24 bytes)
    module_count: u32,        // Number of modules
    index_offset: u64,        // Offset to index (always 128)
    index_size: u64,          // Size of index in bytes
    data_offset: u64,         // Offset where module data begins

    // Hashing (16 bytes)
    library_hash: u64,        // FNV-1a hash of library content
    index_hash: u64,          // FNV-1a hash of index table

    // Reserved (80 bytes)
    reserved2: [u8; 80],      // Padding to 128 bytes
}
```

**Magic Number:** `"LSMF"` (Library Simple Module Format)

**Version:** 1.0
- Major version changes indicate incompatible format changes
- Minor version changes are backward compatible

**Offsets:**
- `index_offset`: Always 128 (immediately after header)
- `data_offset`: `128 + (128 × module_count)`

### Module Index Entry (128 bytes)

```rust
struct ModuleIndexEntry {
    // Module name (64 bytes)
    name: [u8; 64],          // Null-terminated UTF-8 path

    // Location (16 bytes)
    offset: u64,             // Offset to SMF data in file
    size: u64,               // Size of SMF data

    // Metadata (16 bytes)
    hash: u64,               // FNV-1a hash of SMF data
    timestamp: u64,          // Build timestamp (Unix epoch)

    // Reserved (32 bytes)
    reserved: [u8; 32],      // Future extensions
}
```

**Module Name Format:**
- Relative path within library (e.g., `"std/io/mod"`)
- Max 63 characters (64th byte is null terminator)
- UTF-8 encoded
- Case-sensitive

**Hash Verification:**
- FNV-1a hash of complete SMF data
- Used to verify data integrity
- Readers SHOULD verify hash after extraction

## Creating Library SMF Files

### Using LibSmfBuilder

```simple
use compiler.linker.lib_smf_writer.{LibSmfBuilder}

# Create builder
var builder = LibSmfBuilder.new()
builder.set_verbose(true)

# Add modules
builder.add_module("std/io/mod", "path/to/io_mod.smf")
builder.add_module("std/io/file", "path/to/file.smf")
builder.add_module("std/io/dir", "path/to/dir.smf")

# Write library
builder.write("libstd_io.lsm")
```

### Using Convenience Function

```simple
use compiler.linker.lib_smf_writer.{create_lib_smf}

val modules = [
    ("std/io/mod", "io_mod.smf"),
    ("std/io/file", "file.smf"),
    ("std/io/dir", "dir.smf")
]

create_lib_smf(modules, "libstd_io.lsm", true)
```

### Adding In-Memory Data

```simple
var builder = LibSmfBuilder.new()

# Add from in-memory bytes
val smf_data = compile_module("std/io/mod")
builder.add_module_data("std/io/mod", smf_data)

builder.write("output.lsm")
```

## Reading Library SMF Files

### Using LibSmfReader

```simple
use compiler.linker.lib_smf_reader.{LibSmfReader}

# Open library
val reader = LibSmfReader.open("libstd_io.lsm")?
reader.set_verbose(true)

# List modules
val modules = reader.list_modules()
print "Library contains: {modules}"

# Check if module exists
if reader.has_module("std/io/mod"):
    # Get module data
    val smf_data = reader.get_module("std/io/mod")?

    # Use SMF data (pass to SmfReader, etc.)
    process_smf(smf_data)

# Get module metadata
val info = reader.get_module_info("std/io/file")?
print "Module: {info.get_name()}"
print "Size: {info.size} bytes"
print "Hash: {info.hash}"

# Close reader
reader.close()
```

### Unified SMF Getter (Recommended)

The `SmfGetter` provides a unified interface for loading SMF modules from both single files and library archives:

```simple
use compiler.linker.smf_getter.{SmfGetter}

# Create getter with search paths
var getter = SmfGetter.new()
getter.set_verbose(true)

# Add search paths
getter.add_search_path("/usr/lib/simple")
getter.add_search_path("/usr/local/lib/simple")

# Add library archives
getter.add_library("/usr/lib/simple/libstd.lsm")?

# Get module (automatically searches libraries and paths)
val smf_data = getter.get("std/io/mod")?

# Check if module exists
if getter.has_module("std/collections/list"):
    val data = getter.get("std/collections/list")?

# List all available modules
val all_modules = getter.list_modules()

# Get location info
val location = getter.get_location("std/io/mod")?
match location.source_type:
    case SmfSourceType.SingleFile:
        print "Found in: {location.file_path}"
    case SmfSourceType.LibraryFile:
        print "Found in library: {location.file_path} at offset {location.offset}"

# Cleanup
getter.close()
```

## Integration with Module Loader

### Before (Single Files Only)

```simple
# Old approach - only loads single .smf files
val reader = SmfReaderImpl.open("path/to/module.smf")?
val symbol = reader.lookup_symbol("function_name")?
```

### After (Single Files + Libraries)

```simple
# New approach - loads from single files OR libraries
var getter = SmfGetter.new()
getter.add_search_path("/usr/lib/simple")
getter.add_library("/usr/lib/simple/libstd.lsm")?

# Get SMF data (source is transparent)
val smf_data = getter.get("std/io/mod")?

# Create reader from data
val reader = create_smf_reader_from_data(smf_data)?
val symbol = reader.lookup_symbol("function_name")?
```

## Integration with Linker Wrapper

The linker wrapper can now link against library SMF files:

```simple
use compiler.linker.linker_wrapper.*
use compiler.linker.smf_getter.{SmfGetter}

# Setup getter with library paths
var getter = SmfGetter.new()
getter.add_library("libstd.lsm")?

# Link with dependencies from library
link_to_native(
    ["main.o"],
    "app",
    config
)
```

## File Naming Conventions

| Extension | Purpose | Location |
|-----------|---------|----------|
| `.smf` | Single module | Build directory, cache |
| `.lsm` | Library (multiple modules) | `/usr/lib/simple/`, `/usr/local/lib/simple/` |

**Standard Libraries:**
- `libstd.lsm` - Complete standard library
- `libstd_io.lsm` - I/O subsystem
- `libstd_collections.lsm` - Collections subsystem
- `libstd_net.lsm` - Networking subsystem

## Verification and Integrity

### Hash Verification

Library SMF uses FNV-1a hashing for integrity verification:

```simple
# Reading with verification
val reader = LibSmfReader.open("library.lsm")?
val smf_data = reader.get_module("module/name")?
# Hash is automatically verified during get_module()
```

### Library Hash

The library hash covers:
- Complete index table
- All module data
- Excludes header (since header contains the hash)

### Module Hash

Each module has its own hash:
- Computed over complete SMF file data
- Stored in ModuleIndexEntry
- Verified when module is extracted

## Performance Characteristics

### Library Creation (Write)

| Operation | Time Complexity | Notes |
|-----------|----------------|-------|
| Add module | O(1) | In-memory buffer |
| Write library | O(n × m) | n=modules, m=avg size |
| Hash calculation | O(n × m) | FNV-1a is fast |

### Library Reading

| Operation | Time Complexity | Notes |
|-----------|----------------|-------|
| Open library | O(n) | Read and index all entries |
| List modules | O(1) | Cached index |
| Has module | O(n) | Linear search (could use hash map) |
| Get module | O(1) | Direct file seek + read |

**Optimization Opportunities:**
- Use hash map for module index (O(1) lookup)
- Memory-map library file (zero-copy reads)
- Lazy index loading (demand-paged)

## Comparison with Other Formats

### vs .a (ar archives)

| Feature | Library SMF | .a Archives |
|---------|------------|-------------|
| Purpose | SMF modules | Object files |
| Index | Built-in header | Symbol table |
| Random access | Yes (offset table) | Yes (ar format) |
| Compression | Possible | Possible |
| Metadata | Rich (hash, timestamp) | Basic |

### vs .tar

| Feature | Library SMF | .tar |
|---------|------------|------|
| Random access | Yes (indexed) | No (sequential) |
| Module lookup | O(1) | O(n) |
| Metadata | Binary header | Text headers |
| Size overhead | Fixed (128B/module) | Variable |

### vs ZIP

| Feature | Library SMF | ZIP |
|---------|------------|-----|
| Central directory | Index table at start | At end |
| Compression | Per-module possible | Yes |
| Random access | Yes | Yes |
| Complexity | Simple | Complex |

## Future Extensions

### Planned for v1.1

- **Compression:** Per-module compression (zstd, lz4)
- **Signatures:** Digital signatures for verification
- **Dependencies:** Embedded dependency metadata
- **Versioning:** Module version tracking

### Possible for v2.0

- **Lazy loading:** Memory-mapped modules
- **Incremental updates:** Append-only updates
- **Split archives:** Multi-file spanning
- **Encryption:** Encrypted module data

## Tools

### Command-Line Tools

```bash
# Create library
simple lib create -o libstd.lsm std/*.smf

# List modules
simple lib list libstd.lsm

# Extract module
simple lib extract libstd.lsm std/io/mod -o io_mod.smf

# Verify library
simple lib verify libstd.lsm

# Info
simple lib info libstd.lsm
```

### Library Management

```bash
# Add module to existing library
simple lib add libstd.lsm std/new/mod.smf

# Remove module
simple lib remove libstd.lsm std/old/mod

# Optimize (rebuild with better layout)
simple lib optimize libstd.lsm -o libstd_opt.lsm
```

## Implementation Files

| File | Purpose |
|------|---------|
| `src/compiler/linker/lib_smf.spl` | Format definitions (header, index) |
| `src/compiler/linker/lib_smf_writer.spl` | Create library archives |
| `src/compiler/linker/lib_smf_reader.spl` | Read library archives |
| `src/compiler/linker/smf_getter.spl` | Unified loader (files + libraries) |
| `src/compiler/linker/test/lib_smf_spec.spl` | Test suite |

## See Also

- **SMF Specification:** `doc/format/smf_specification.md`
- **Module Loading:** `doc/guide/module_loading.md`
- **Linker Wrapper:** `src/compiler/linker/linker_wrapper.spl`

---

**Authors:** Simple Language Team
**License:** MIT
**Last Updated:** 2026-02-09
