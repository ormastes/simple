# JIT Infrastructure Guide

**Status:** Simple implementation complete (Rust FFI pending)

---

## Architecture

```
Simple Source → Shared Compiler Pipeline → Backend
                (Parser → HIR → MIR)       ├─ AOT: Write to disk
                                            └─ JIT: Load into memory
```

JIT reuses the same compiler pipeline as AOT. The JIT wrapper is a thin orchestration layer (~1000 lines) coordinating existing components.

---

## Using the SMF Cache

```simple
use compiler.loader.smf_cache (SmfCache)

var cache = SmfCache.new()
val mapped_smf = cache.get("path/to/file.smf")?
val metadata = mapped_smf.read_note_sdn()?
val template = mapped_smf.read_template_bytes("symbol_name", offset)?
cache.prefetch(["file1.smf", "file2.smf", "file3.smf"])
cache.clear()
```

| Method | Description |
|--------|-------------|
| `SmfCache.new()` | Create new cache |
| `get(path)` | Get/load SMF file |
| `prefetch(paths)` | Prefetch multiple files |
| `clear()` | Unmap all files |
| `get_stats()` | Get cache statistics |

---

## Using JIT Instantiator

```simple
use compiler.loader.jit_instantiator (JitInstantiator, JitInstantiatorConfig)

val config = JitInstantiatorConfig(
    update_smf: true, max_depth: 50, enabled: true, verbose: false
)
var jit = JitInstantiator.new(config)
jit.load_smf_metadata("path/to/file.smf")?

val result = jit.try_jit_instantiate("fn$Vec$i64")
match result:
    case Success(code, symbol, address): print "JIT compiled {symbol}"
    case NotFound(symbol): print "Symbol {symbol} not found"
    case CompilationError(msg): print "Compilation failed: {msg}"
    case CircularDependency(cycle): print "Circular dependency: {cycle}"
```

| Method | Description |
|--------|-------------|
| `JitInstantiator.new(config)` | Create instantiator |
| `load_smf_metadata(path)` | Load SMF metadata |
| `try_jit_instantiate(symbol)` | Try JIT compile |
| `can_jit_instantiate(symbol)` | Check if symbol can be JIT'd |
| `stats()` | Get statistics |

---

## Executable Memory

```simple
use app.io.mod (alloc_exec_memory, write_exec_memory, flush_icache, get_function_pointer)

val code: [u8] = [0x48, 0xc7, 0xc0, 0x2a, 0x00, 0x00, 0x00, 0xc3]  # mov rax, 42; ret
val address = alloc_exec_memory(code.len() as i64)
write_exec_memory(address, code, offset: 0)
flush_icache(address, code.len() as i64)    # Required on ARM/RISC-V
val result = call_function_0(get_function_pointer(address))
```

### W^X Security (Production)

```simple
use app.io.mod (alloc_rw_memory, make_executable)

val address = alloc_rw_memory(size)          # 1. Allocate RW (no execute)
write_exec_memory(address, code, 0)          # 2. Write code
make_executable(address, size)               # 3. RW -> RX (removes write)
```

---

## mmap Operations

```simple
use app.io.mod (mmap_file, munmap, mmap_read_bytes)

val PROT_READ: i32 = 0x1
val MAP_PRIVATE: i32 = 0x2

val (address, size) = mmap_file(path: "data.bin", prot: PROT_READ, flags: MAP_PRIVATE, offset: 0, length: 0)
val data = mmap_read_bytes(address, offset: 100, length: 256)
munmap(address, size)
```

---

## Common Patterns

### Load-Time JIT Fallback

```simple
fn resolve_symbol(name: text, jit: JitInstantiator) -> i64?:
    if symbol_table.contains_key(name):
        return Some(symbol_table[name])
    val result = jit.try_jit_instantiate(name)
    match result:
        case Success(_, _, address): return address
        case _: return None
```

### Batch Template Loading

```simple
fn load_module_templates(module_path: text, jit: JitInstantiator):
    val mapped = jit.smf_cache.get(module_path)?
    val metadata = mapped.read_note_sdn()?
    for entry in metadata.possible:
        val _ = jit.try_jit_instantiate(entry.mangled_name)
```

---

## Performance

| Operation | Target |
|-----------|--------|
| Manager Creation | < 1ms |
| Simple Function Compile | < 10ms (Cranelift, opt=0) |
| Simple Function Execute | < 1us (native speed) |
| Complex Function Compile | < 100ms (Cranelift, opt=2) |

**Tips:** Use `cache.prefetch()` at startup. Use `madvise(addr, size, MADV_SEQUENTIAL)` for sequential reads. Use `mlock()` for hot code.

---

## See Also

- [capabilities.md](capabilities.md) - Backend selection (Cranelift vs LLVM)
- **Source:** `src/compiler/loader/smf_cache.spl`, `src/compiler/loader/jit_instantiator.spl`
- **Tests:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
- **Report:** `doc/report/jit_infrastructure_implementation_2026-02-04.md`
