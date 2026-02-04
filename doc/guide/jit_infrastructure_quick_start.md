# JIT Infrastructure Quick Start Guide

**Status:** ✅ Simple implementation complete (Rust FFI pending)
**Date:** 2026-02-04

## Overview

The JIT (Just-In-Time) infrastructure enables load-time template instantiation using:
- **mmap** for zero-copy file access
- **Executable memory** for JIT-compiled code
- **Auto-loading cache** for efficient SMF file management

## Quick Start

### 1. Using the SMF Cache

```simple
use compiler.loader.smf_cache (SmfCache)

# Create cache
var cache = SmfCache.new()

# Load SMF file (auto-caches)
val mapped_smf = cache.get("path/to/file.smf")?

# Read metadata
val metadata = mapped_smf.read_note_sdn()?

# Read template bytes
val template = mapped_smf.read_template_bytes("symbol_name", offset)?

# Prefetch multiple files
cache.prefetch(["file1.smf", "file2.smf", "file3.smf"])

# Get statistics
val stats = cache.get_stats()
print "Cache hits: {stats.cache_hits}, misses: {stats.cache_misses}"

# Cleanup
cache.clear()
```

### 2. Using JIT Instantiator

```simple
use compiler.loader.jit_instantiator (JitInstantiator, JitInstantiatorConfig)

# Configure JIT
val config = JitInstantiatorConfig(
    update_smf: true,    # Update SMF files with results
    max_depth: 50,       # Maximum recursion depth
    enabled: true,       # Enable JIT compilation
    verbose: false       # Verbose logging
)

# Create JIT instantiator
var jit = JitInstantiator.new(config)

# Load SMF metadata
jit.load_smf_metadata("path/to/file.smf")?

# Try JIT instantiation
val result = jit.try_jit_instantiate("fn$Vec$i64")

match result:
    case Success(code, symbol, address):
        print "JIT compiled {symbol} at address {address}"
        # Use the function pointer

    case NotFound(symbol):
        print "Symbol {symbol} not found"

    case CompilationError(msg):
        print "Compilation failed: {msg}"

    case CircularDependency(cycle):
        print "Circular dependency: {cycle}"

# Get statistics
val stats = jit.stats()
print "Cached: {stats.cached_count}"
print "SMF files: {stats.smf_files_mapped}"
print "Memory: {stats.smf_memory_mapped} bytes"
```

### 3. Using mmap Directly

```simple
use app.io.mod (mmap_file, munmap, mmap_read_bytes)

# Protection flags
val PROT_READ: i32 = 0x1
val MAP_PRIVATE: i32 = 0x2

# Map file
val (address, size) = mmap_file(
    path: "data.bin",
    prot: PROT_READ,
    flags: MAP_PRIVATE,
    offset: 0,
    length: 0  # 0 = entire file
)

if address != 0:
    # Read data
    val data = mmap_read_bytes(address, offset: 100, length: 256)

    # Unmap when done
    munmap(address, size)
```

### 4. Using Executable Memory

```simple
use app.io.mod (alloc_exec_memory, write_exec_memory, flush_icache, get_function_pointer)

# Compiled code bytes (from JIT compiler)
val code: [u8] = [0x48, 0xc7, 0xc0, 0x2a, 0x00, 0x00, 0x00, 0xc3]  # mov rax, 42; ret

# Allocate executable memory
val address = alloc_exec_memory(code.len() as i64)

if address != 0:
    # Write code
    val written = write_exec_memory(address, code, offset: 0)

    # Flush instruction cache (required on ARM/RISC-V)
    flush_icache(address, code.len() as i64)

    # Get function pointer
    val fn_ptr = get_function_pointer(address)

    # Call it (returns 42)
    val result = call_function_0(fn_ptr)
    print "Result: {result}"
```

### 5. W^X Security (Production)

For production, use Write-XOR-Execute (W^X) security:

```simple
use app.io.mod (alloc_rw_memory, make_executable)

# 1. Allocate RW memory (no execute)
val address = alloc_rw_memory(size)

# 2. Write code
write_exec_memory(address, code, 0)

# 3. Make executable (removes write permission)
make_executable(address, size)

# 4. Now can execute, but cannot write
val fn_ptr = get_function_pointer(address)
```

## API Reference

### SmfCache

| Method | Description |
|--------|-------------|
| `SmfCache.new()` | Create new cache |
| `get(path)` | Get/load SMF file |
| `prefetch(paths)` | Prefetch multiple files |
| `clear()` | Unmap all files |
| `get_stats()` | Get cache statistics |
| `is_cached(path)` | Check if file is cached |
| `cached_count()` | Number of cached files |

### MappedSmf

| Method | Description |
|--------|-------------|
| `read_note_sdn()` | Read metadata |
| `read_template_bytes(symbol, offset)` | Read template code |
| `read_section(index)` | Read section data |
| `close()` | Unmap file |

### JitInstantiator

| Method | Description |
|--------|-------------|
| `JitInstantiator.new(config)` | Create instantiator |
| `load_smf_metadata(path)` | Load SMF metadata |
| `try_jit_instantiate(symbol)` | Try JIT compile |
| `can_jit_instantiate(symbol)` | Check if symbol can be JIT'd |
| `find_possible(symbol)` | Find template entry |
| `stats()` | Get statistics |

### mmap Operations

| Function | Description |
|----------|-------------|
| `mmap_file(path, prot, flags, offset, len)` | Map file |
| `munmap(address, size)` | Unmap file |
| `mmap_read_bytes(addr, offset, len)` | Read bytes |
| `mmap_read_string(addr, offset, max_len)` | Read string |
| `msync(addr, size, is_async)` | Sync to disk |
| `mlock(addr, size)` | Lock in RAM |
| `madvise(addr, size, advice)` | Memory advice |

### Executable Memory

| Function | Description |
|----------|-------------|
| `alloc_exec_memory(size)` | Allocate RWX memory |
| `alloc_rw_memory(size)` | Allocate RW memory (W^X) |
| `write_exec_memory(addr, code, offset)` | Write code |
| `make_executable(addr, size)` | RW → RX (W^X) |
| `flush_icache(addr, size)` | Flush instruction cache |
| `get_function_pointer(addr)` | Get function pointer |
| `call_function_0/1/2(fn_ptr, ...)` | Call function |
| `free_exec_memory(addr, size)` | Free memory |

## Constants

### Protection Flags (mmap)

```simple
val PROT_NONE: i32 = 0x0   # No access
val PROT_READ: i32 = 0x1   # Read
val PROT_WRITE: i32 = 0x2  # Write
val PROT_EXEC: i32 = 0x4   # Execute
```

### Mapping Flags (mmap)

```simple
val MAP_SHARED: i32 = 0x1      # Share changes
val MAP_PRIVATE: i32 = 0x2     # Private copy
val MAP_ANONYMOUS: i32 = 0x20  # No file
val MAP_FIXED: i32 = 0x10      # Fixed address
```

### Memory Advice (madvise)

```simple
val MADV_NORMAL: i32 = 0      # No special treatment
val MADV_RANDOM: i32 = 1      # Random access
val MADV_SEQUENTIAL: i32 = 2  # Sequential access
val MADV_WILLNEED: i32 = 3    # Will need soon (prefetch)
val MADV_DONTNEED: i32 = 4    # Won't need (can free)
```

## Performance Tips

### 1. Prefetch Files

```simple
# Prefetch multiple SMF files at startup
cache.prefetch([
    "module1.smf",
    "module2.smf",
    "module3.smf"
])
```

### 2. Use Sequential Advice

```simple
# For sequential reads
madvise(address, size, MADV_SEQUENTIAL)

# For random reads
madvise(address, size, MADV_RANDOM)
```

### 3. Lock Hot Code in RAM

```simple
# Prevent swapping of frequently used code
mlock(exec_address, code_size)
```

### 4. Monitor Cache Performance

```simple
val stats = cache.get_stats()
val hit_rate = stats.cache_hits as f64 / (stats.cache_hits + stats.cache_misses) as f64
print "Cache hit rate: {hit_rate * 100.0}%"
```

## Common Patterns

### Pattern 1: Load-Time JIT

```simple
# Symbol resolution with JIT fallback
fn resolve_symbol(name: text, jit: JitInstantiator) -> i64?:
    # Try primary symbol table first
    if symbol_table.contains_key(name):
        return Some(symbol_table[name])

    # JIT compile if possible
    val result = jit.try_jit_instantiate(name)
    match result:
        case Success(_, _, address):
            return address
        case _:
            return None
```

### Pattern 2: Batch Template Loading

```simple
# Load templates for entire module at once
fn load_module_templates(module_path: text, jit: JitInstantiator):
    val mapped = jit.smf_cache.get(module_path)?
    val metadata = mapped.read_note_sdn()?

    # Pre-compile all templates
    for entry in metadata.possible:
        val _ = jit.try_jit_instantiate(entry.mangled_name)
```

### Pattern 3: Memory-Mapped Data Structure

```simple
# Read complex data structures from mmap
fn read_smf_header(mapped: MappedSmf) -> SmfHeader:
    val header_bytes = mmap_read_bytes(
        mapped.address,
        mapped.size - 128,  # Header at end
        128
    )
    parse_header(header_bytes)
```

## Troubleshooting

### "Failed to mmap file"

**Causes:**
- File doesn't exist
- No read permission
- Out of virtual memory

**Solution:**
```simple
val result = cache.get(path)
match result:
    case Ok(mapped): # use mapped
    case Err(msg): print "Error: {msg}"
```

### "Failed to allocate executable memory"

**Causes:**
- Out of memory
- System doesn't allow RWX pages
- Address space exhausted

**Solution:**
```simple
# Use W^X instead of RWX
val addr = alloc_rw_memory(size)
write_exec_memory(addr, code, 0)
make_executable(addr, size)
```

### "Symbol not found in metadata"

**Causes:**
- Template not in SMF file
- Wrong SMF file loaded
- Metadata not up to date

**Solution:**
```simple
# Check if symbol is available
if jit.can_jit_instantiate(symbol):
    val result = jit.try_jit_instantiate(symbol)
else:
    print "Symbol {symbol} not available for JIT"
```

## Next Steps

1. **Implement Rust FFI** - See `doc/report/jit_infrastructure_implementation_2026-02-04.md`
2. **Run tests** - `simple test test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
3. **Integrate into loader** - Use `JitSymbolResolver` for automatic JIT fallback

## See Also

- **Implementation Report:** `doc/report/jit_infrastructure_implementation_2026-02-04.md`
- **FFI Specs:** `src/app/ffi_gen/specs/mmap.spl`, `src/app/ffi_gen/specs/exec_memory.spl`
- **Source:** `src/compiler/loader/smf_cache.spl`, `src/compiler/loader/jit_instantiator.spl`
- **Tests:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
