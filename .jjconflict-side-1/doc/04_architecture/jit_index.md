# JIT Infrastructure - Complete Documentation Index

**Status:** ✅ Active loader/JIT path in use | ✅ Shared cache + shared mapper wired | ⚠️ Full-suite `/verify` still separate
**Date:** 2026-03-31

## Quick Links

| Document | Purpose | Status |
|----------|---------|--------|
| **[JIT Guide](guide/backend/jit.md)** | Developer guide with examples | ✅ Complete |
| **[Implementation Report](report/jit_infrastructure_implementation_2026-02-04.md)** | Technical details and architecture | ✅ Complete |
| **[Rust FFI Plan](plan/rust_ffi_implementation_plan.md)** | Next steps for Rust implementation | 📋 Ready |

## What Was Implemented

### ✅ Complete (Simple Side)

**1. mmap-Based File I/O**
- File: `src/app/ffi_gen/specs/mmap.spl`
- Zero-copy file access
- 10 FFI functions + wrappers
- Status: ✅ Compiles successfully

**2. Executable Memory Allocation**
- File: `src/app/ffi_gen/specs/exec_memory.spl`
- JIT code execution
- 16 FFI functions + wrappers
- Status: ✅ Compiles successfully

**3. SMF File Cache**
- File: `src/compiler/99.loader/loader/smf_cache.spl`
- Auto-loading shared cache path used by JIT metadata reads
- Statistics tracking
- Status: ✅ Active in loader/JIT path

**4. JitInstantiator Updates**
- File: `src/compiler/99.loader/loader/jit_instantiator.spl`
- Uses the shared cache path instead of local stub cache structures
- Uses the shared executable mapper / JitMapper for mapped code
- Status: ✅ Active in loader/JIT path

**5. Documentation**
- Quick start guide (400+ lines)
- Implementation report (750+ lines)
- API reference with examples
- Status: ✅ Complete

### ✅ Verified in Current Refactor

**1. Loader/JIT Integration**
- Shared cache-backed metadata reads
- Shared executable mapper for loader + JIT
- Status: ✅ Covered by targeted loader/JIT tests

**2. Loader Relocation Path**
- Module load applies relocations before publish
- Provider-backed module bytes are used for relocation source data
- Status: ✅ Covered by relocation regression tests

## File Locations

### Source Files

```
src/
├── app/
│   ├── ffi_gen/specs/
│   │   ├── mmap.spl                 # ✅ mmap FFI declarations
│   │   └── exec_memory.spl          # ✅ Executable memory FFI
│   └── io/
│       └── mod.spl                   # ✅ Updated with new exports
│
└── compiler/
    └── 99.loader/
        └── loader/
            ├── smf_cache.spl             # ✅ Shared SMF cache path
            ├── jit_instantiator.spl      # ✅ Shared cache + shared mapper
            └── module_loader.spl         # ✅ Relocation-aware load path
```

### Documentation

```
doc/
├── JIT_INFRASTRUCTURE_INDEX.md       # ✅ This file
├── guide/
│   └── backend/jit.md                    # ✅ Developer guide
├── report/
│   └── jit_infrastructure_implementation_2026-02-04.md  # ✅ Details
└── plan/
    └── rust_ffi_implementation_plan.md    # 📋 Next steps
```

### Tests

```
test/
├── compiler/
│   └── jit_infrastructure_smoke_test.spl  # ✅ Basic API test
└── unit/compiler/loader/
    ├── jit_instantiator_spec.spl          # ✅ Active targeted coverage
    ├── module_loader_spec.spl             # ✅ Loader/JIT integration coverage
    └── module_loader_relocation_spec.spl  # ✅ Real relocation-bearing SMF coverage
```

## API Overview

### Core Types

```simple
# Configuration
JitInstantiatorConfig(update_smf, max_depth, enabled, verbose)

# Main classes
JitInstantiator    # JIT compilation engine
SmfCache           # Memory-mapped file cache
MappedSmf          # Single cached SMF file

# Results
JitInstantiationResult:
    Success(code, symbol, address)
    NotFound(symbol)
    CircularDependency(cycle)
    CompilationError(message)
    UpdateFailed(symbol, error)
```

### Key Operations

```simple
# Cache management
cache.get(path)              # Load/get SMF file
cache.prefetch(paths)        # Prefetch multiple files
cache.clear()                # Unmap all

# JIT compilation
jit.try_jit_instantiate(symbol)      # Try JIT compile
jit.can_jit_instantiate(symbol)      # Check availability
jit.load_smf_metadata(path)          # Load metadata

# Memory operations
mmap_file(path, prot, flags, offset, len)  # Map file
alloc_exec_memory(size)                     # Allocate RWX
write_exec_memory(addr, code, offset)       # Write code
get_function_pointer(addr)                  # Get fn pointer
```

## Statistics

### Code Metrics

| Component | Lines | Language | Status |
|-----------|-------|----------|--------|
| mmap.spl | 146 | Simple | ✅ Complete |
| exec_memory.spl | 177 | Simple | ✅ Complete |
| smf_cache.spl | 272 | Simple | ✅ Complete |
| jit_instantiator.spl (changes) | ~100 | Simple | ✅ Complete |
| io/mod.spl (changes) | ~150 | Simple | ✅ Complete |
| **Total Simple** | **~845** | | ✅ |
| | | | |
| mmap.rs (pending) | ~300 | Rust | 📋 Planned |
| exec_memory.rs (pending) | ~400 | Rust | 📋 Planned |
| **Total Rust** | **~700** | | 📋 |
| | | | |
| **Grand Total** | **~1,545** | | |

### Test Impact

- `test/unit/compiler/loader/jit_instantiator_spec.spl`
- `test/unit/compiler/loader/module_loader_spec.spl`
- `test/unit/compiler/loader/module_loader_relocation_spec.spl`
- `test/unit/compiler/loader/object_mapper_spec.spl`
- Status: targeted loader/JIT verification passed in the refactor sweep

## Getting Started

### For Simple Developers

See [JIT Guide](guide/backend/jit.md) for:
- Using SmfCache
- Using JitInstantiator
- Direct mmap operations
- Executable memory allocation
- Complete API reference

### For Rust Implementers

See [Rust FFI Implementation Plan](plan/rust_ffi_implementation_plan.md) for:
- Detailed implementation guide
- Code examples for each function
- Testing strategy
- Estimated time: 8-11 hours

## Example Usage

### Basic JIT Compilation

```simple
use compiler.loader.jit_instantiator (JitInstantiator, JitInstantiatorConfig)

# Configure
val config = JitInstantiatorConfig(
    update_smf: true,
    max_depth: 50,
    enabled: true,
    verbose: false
)

# Create
var jit = JitInstantiator.new(config)

# Load metadata
jit.load_smf_metadata("module.smf")?

# JIT compile
val result = jit.try_jit_instantiate("fn$Vec$i64")

match result:
    case Success(code, symbol, address):
        print "Compiled {symbol} at {address}"
    case NotFound(symbol):
        print "Symbol not found: {symbol}"
    case CompilationError(msg):
        print "Error: {msg}"
```

### File Caching

```simple
use compiler.loader.smf_cache (SmfCache)

# Create cache
var cache = SmfCache.new()

# Load file (auto-caches)
val mapped = cache.get("file.smf")?

# Read metadata
val metadata = mapped.read_note_sdn()?
print "Found {metadata.possible.len()} templates"

# Statistics
val stats = cache.stats()
print "Hit rate: {stats.cache_hits}/{stats.cache_hits + stats.cache_misses}"
```

## Next Steps

1. Run broader repo `/verify` before release work.
2. Expand platform/backend coverage only when new linker targets need it.
3. Keep this index aligned with the active `src/compiler/99.loader/loader/*` paths rather than the older flattened loader paths.

4. **Test** (1-2 hours)
   - Rust unit tests
   - Simple integration tests
   - Verify 44 tests pass

### Future Enhancements

- [ ] Parallel prefetching
- [ ] LRU cache eviction
- [ ] Compressed SMF support
- [ ] Async file loading
- [ ] More call conventions (3+ args)
- [ ] Platform-specific optimizations

## Performance Expectations

### mmap Performance

- **Cache hit:** O(1) hash lookup
- **Cache miss:** ~1 syscall + O(n) parse
- **Memory overhead:** ~128 bytes/file + mmap region (shared)
- **Access speed:** Direct memory (zero-copy)

### JIT Compilation

- **First compile:** Full compilation + memory allocation
- **Cached compile:** O(1) lookup, instant return
- **Memory per function:** Code size + alignment padding

### Expected Metrics

- Cache hit rate: >90% in typical workload
- JIT compile time: 1-10ms per template
- Memory overhead: <1% of process memory
- Zero-copy reads: ~100x faster than traditional I/O

## Security Considerations

### Current (Development)

- ✅ Read-only mmap for data files
- ⚠️ RWX memory for JIT code (simpler for development)
- ✅ No PROT_EXEC on data files

### Production (TODO)

- 🔒 W^X (Write-XOR-Execute) for JIT code
- 🔒 Validate code before execution
- 🔒 Limit maximum JIT memory
- 🔒 Audit JIT compilation events

## Troubleshooting

### Common Issues

**"Failed to mmap file"**
- Check file exists and is readable
- Verify not out of virtual memory
- See: Quick Start Guide, Troubleshooting section

**"Failed to allocate executable memory"**
- System may not allow RWX pages
- Use W^X pattern instead
- See: Rust FFI Plan, Issue 1

**"Symbol not found"**
- Template may not be in SMF file
- Check metadata with `cache.get(path)?.read_note_sdn()`
- See: Quick Start Guide, Pattern 2

## Support

- **Questions:** See Quick Start Guide
- **Implementation:** See Rust FFI Implementation Plan
- **Details:** See Implementation Report
- **Bugs:** File issue with tag `jit-infrastructure`

## References

### External Documentation

- **mmap(2):** Linux man page for memory mapping
- **mprotect(2):** Linux man page for memory protection
- **W^X:** Write-XOR-Execute security model

### Related Codebase

- SMF format: `doc/05_design/smf_note_sdn_implementation.md`
- SDN parser: `src/lib/sdn/parser.spl`
- Note.sdn: `src/compiler/monomorphize/note_sdn.spl`

---

**Status Summary:**
- ✅ **Simple Implementation:** 100% complete
- 📋 **Rust FFI:** Plan ready, implementation pending
- 🎯 **Estimated Time to Complete:** 8-11 hours
- 🧪 **Tests Ready:** 44 tests waiting for FFI

**Last Updated:** 2026-02-04
