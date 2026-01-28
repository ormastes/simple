# Shared Type Inference Implementation Plan

## Overview

Make type inference shareable across compiler, loader, linker, and interpreter with link-time instantiation.

**Implementation Principle**: Simple language unless performance-critical binary I/O.

---

## Architecture Summary

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     SIMPLE LANGUAGE COMPONENTS                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  simple/compiler/inference/          simple/compiler/linker/            │
│  ┌─────────────────────────┐        ┌─────────────────────────┐        │
│  │ types.spl               │        │ obj_taker.spl           │        │
│  │ unify.spl               │◄───────│ smf_reader.spl          │        │
│  │ infer.spl               │        │ smf_writer.spl          │        │
│  │ constraints.spl         │        │ link.spl                │        │
│  │ deferred.spl            │        │ mold.spl                │        │
│  │ serialize.spl           │        │ note_sdn.spl            │        │
│  └─────────────────────────┘        └─────────────────────────┘        │
│              │                                  │                       │
│              └──────────────┬───────────────────┘                       │
│                             │                                           │
│                             ▼                                           │
│                 simple/compiler/loader/                                 │
│                 ┌─────────────────────────┐                            │
│                 │ module_loader.spl       │                            │
│                 │ instantiate.spl         │                            │
│                 └─────────────────────────┘                            │
│                                                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                     RUST FFI (Binary I/O only)                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  src/rust/loader/src/smf/ffi.rs    src/rust/compiler/src/linker/       │
│  ┌─────────────────────────┐       ┌─────────────────────────┐         │
│  │ smf_reader_open()       │       │ mold_find_path()        │         │
│  │ smf_reader_read_header()│       │ mold_execute()          │         │
│  │ smf_reader_read_section()       │ write_elf_object()      │         │
│  │ smf_reader_close()      │       └─────────────────────────┘         │
│  └─────────────────────────┘                                           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Type Inference Module (Simple)

### Goal
Create shared type inference engine in Simple language.

### Directory Structure

```
simple/compiler/inference/
├── __init__.spl          # Module exports
├── types.spl             # Type enum and TypeVarId
├── unify.spl             # Unification algorithm
├── infer.spl             # Inference engine
├── constraints.spl       # Constraint system
├── deferred.spl          # Deferred hints
└── serialize.spl         # SDN serialization
```

### Tasks

| ID | Task | File | Est |
|----|------|------|-----|
| 1.1 | Create module __init__.spl with exports | `inference/__init__.spl` | 1h |
| 1.2 | Define Type enum with all variants | `inference/types.spl` | 4h |
| 1.3 | Define TypeVarId, DeferredTypeId, Constraint | `inference/types.spl` | 2h |
| 1.4 | Implement Unifier class with fresh_var() | `inference/unify.spl` | 2h |
| 1.5 | Implement unify() method | `inference/unify.spl` | 4h |
| 1.6 | Implement resolve() and occurs_check() | `inference/unify.spl` | 2h |
| 1.7 | Implement InferenceEngine class | `inference/infer.spl` | 4h |
| 1.8 | Implement infer_expr() for all expr types | `inference/infer.spl` | 6h |
| 1.9 | Implement TypeEnv (scope/lookup) | `inference/infer.spl` | 2h |
| 1.10 | Define Constraint enum | `inference/constraints.spl` | 2h |
| 1.11 | Implement constraint generation | `inference/constraints.spl` | 4h |
| 1.12 | Implement constraint solving | `inference/constraints.spl` | 4h |
| 1.13 | Implement DeferredHint struct | `inference/deferred.spl` | 2h |
| 1.14 | Implement generate_deferred_hints() | `inference/deferred.spl` | 2h |
| 1.15 | Implement apply_deferred() | `inference/deferred.spl` | 4h |
| 1.16 | Implement SDN serialization | `inference/serialize.spl` | 4h |
| 1.17 | Write unit tests | `test/lib/std/unit/compiler/inference_spec.spl` | 8h |

### Key Types

```simple
# types.spl
enum Type:
    Int(bits: i32, signed: bool)
    Float(bits: i32)
    Bool, Str, Nil
    Var(id: TypeVarId)
    Skolem(id: SkolemId)
    Function(params: List<Type>, ret: Type)
    Array(elem: Type, size: Option<i64>)
    Tuple(elements: List<Type>)
    Optional(inner: Type)
    Struct(name: text, fields: List<Field>, type_params: List<Type>)
    Enum(name: text, variants: List<Variant>, type_params: List<Type>)
    Generic(base: text, args: List<Type>)
    TypeParam(name: text)
    Deferred(id: DeferredTypeId, constraints: List<Constraint>, fallback: Option<Type>)

enum Constraint:
    Equals(Type, Type)
    Subtype(Type, Type)
    HasField(Type, text, Type)
    HasMethod(Type, text, FunctionType)
    Implements(Type, text)
    Numeric(Type)
    Iterable(Type, Type)
```

### Test Cases

```simple
# test/lib/std/unit/compiler/inference_spec.spl

describe "Type Inference":
    describe "Unification":
        it "unifies identical types":
            val u = Unifier.empty()
            u.unify(Type.Int(64, true), Type.Int(64, true)).is_ok()
                .should_be(true)

        it "unifies type variable with concrete":
            val u = Unifier.empty()
            val tv = u.fresh_var()
            u.unify(tv, Type.Int(64, true)).is_ok().should_be(true)
            u.resolve(tv).should_eq(Type.Int(64, true))

        it "detects infinite type (occurs check)":
            val u = Unifier.empty()
            val tv = u.fresh_var()
            val arr = Type.Array(elem: tv, size: None)
            u.unify(tv, arr).is_err().should_be(true)

    describe "Inference":
        it "infers literal types":
            val engine = InferenceEngine.create()
            engine.infer_expr(Expr.Literal(Literal.Int(42)))
                .should_eq(Ok(Type.Int(64, true)))

        it "infers identity function":
            val engine = InferenceEngine.create()
            val lambda = Expr.Lambda(
                params: [Param(name: "x", ty: None)],
                body: Expr.Identifier("x")
            )
            val ty = engine.infer_expr(lambda)?
            # Should be Function([Var(0)], Var(0))
            ty.is_function().should_be(true)
```

---

## Phase 2: ObjTaker (Simple)

### Goal
Create shared object extraction component that uses type inference.

### Tasks

| ID | Task | File | Est |
|----|------|------|-----|
| 2.1 | Create ObjTaker class | `linker/obj_taker.spl` | 2h |
| 2.2 | Implement take_object() routing | `linker/obj_taker.spl` | 2h |
| 2.3 | Implement take_generic() | `linker/obj_taker.spl` | 4h |
| 2.4 | Implement take_deferred() | `linker/obj_taker.spl` | 4h |
| 2.5 | Implement take_concrete() | `linker/obj_taker.spl` | 2h |
| 2.6 | Implement template loading | `linker/obj_taker.spl` | 4h |
| 2.7 | Implement type arg inference | `linker/obj_taker.spl` | 4h |
| 2.8 | Implement instantiate() | `linker/obj_taker.spl` | 4h |
| 2.9 | Add template cache | `linker/obj_taker.spl` | 2h |
| 2.10 | Add instance cache | `linker/obj_taker.spl` | 2h |
| 2.11 | Write tests | `test/lib/std/unit/compiler/obj_taker_spec.spl` | 6h |

### ObjTaker API

```simple
class ObjTaker:
    inference: InferenceEngine
    template_cache: Dict<text, Template>
    instance_cache: Dict<text, ResolvedObject>
    smf_reader: SmfReader

    static fn create(smf_reader: SmfReader) -> ObjTaker

    # Main entry point
    fn take_object(symbol_name: text) -> Result<ResolvedObject, ObjTakeError>

    # Specific handlers
    fn take_generic(symbol: SmfSymbol) -> Result<ResolvedObject, ObjTakeError>
    fn take_deferred(symbol: SmfSymbol) -> Result<ResolvedObject, ObjTakeError>
    fn take_concrete(symbol: SmfSymbol) -> Result<ResolvedObject, ObjTakeError>

    # Helpers
    fn load_template(symbol: SmfSymbol) -> Result<Template, ObjTakeError>
    fn infer_type_args(template: Template, hints: InferenceHints) -> Result<List<Type>, ObjTakeError>
    fn instantiate(template: Template, type_args: List<Type>) -> Result<ResolvedObject, ObjTakeError>

    # Caching
    fn clear_cache()
    fn cache_stats() -> CacheStats
```

---

## Phase 3: SMF Reader/Writer (Simple + Rust FFI)

### Goal
Create Simple wrappers for SMF with minimal Rust FFI for binary I/O.

### Tasks

| ID | Task | File | Lang | Est |
|----|------|------|------|-----|
| 3.1 | Add SectionType.InferenceHints | `smf/section.rs` | Rust | 1h |
| 3.2 | Create SmfReaderFfi extern class | `linker/smf_reader.spl` | Simple | 2h |
| 3.3 | Implement SmfReader class | `linker/smf_reader.spl` | Simple | 4h |
| 3.4 | Implement symbol lookup | `linker/smf_reader.spl` | Simple | 2h |
| 3.5 | Implement inference hints loading | `linker/smf_reader.spl` | Simple | 4h |
| 3.6 | Implement Rust FFI functions | `smf/ffi.rs` | Rust | 4h |
| 3.7 | Create SmfWriterFfi extern class | `linker/smf_writer.spl` | Simple | 2h |
| 3.8 | Implement SmfWriter class | `linker/smf_writer.spl` | Simple | 4h |
| 3.9 | Implement note.sdn parser | `linker/note_sdn.spl` | Simple | 4h |
| 3.10 | Implement note.sdn writer | `linker/note_sdn.spl` | Simple | 2h |
| 3.11 | Write tests | `test/lib/std/unit/compiler/smf_spec.spl` | Simple | 6h |

### Rust FFI Surface (Minimal)

```rust
// src/rust/loader/src/smf/ffi.rs

use std::ffi::{c_char, CStr};
use std::ptr;

#[repr(C)]
pub struct SmfReaderHandle {
    inner: Box<SmfReaderInner>,
}

#[repr(C)]
pub struct ByteBuffer {
    data: *const u8,
    len: usize,
}

#[repr(C)]
pub struct SmfHeaderRaw {
    magic: [u8; 4],
    version_major: u8,
    version_minor: u8,
    section_count: u32,
    symbol_count: u32,
    // ... other fields as C-compatible types
}

#[no_mangle]
pub extern "C" fn smf_reader_open(path: *const c_char) -> *mut SmfReaderHandle {
    let path = unsafe { CStr::from_ptr(path) }.to_str().ok()?;
    // Open file and create reader
    // Return handle or null
}

#[no_mangle]
pub extern "C" fn smf_reader_read_header(handle: *mut SmfReaderHandle) -> SmfHeaderRaw {
    // Read and return header
}

#[no_mangle]
pub extern "C" fn smf_reader_read_section(
    handle: *mut SmfReaderHandle,
    index: u32,
) -> ByteBuffer {
    // Read section data
}

#[no_mangle]
pub extern "C" fn smf_reader_close(handle: *mut SmfReaderHandle) {
    if !handle.is_null() {
        unsafe { drop(Box::from_raw(handle)); }
    }
}
```

### Simple Wrapper

```simple
# simple/compiler/linker/smf_reader.spl

extern class SmfReaderFfi:
    static fn open(path: text) -> Result<SmfReaderFfi, SmfError>
    fn read_header() -> SmfHeaderRaw
    fn read_section(index: i32) -> bytes
    fn read_symbol_table() -> List<SmfSymbolRaw>
    fn close()

class SmfReader:
    ffi: SmfReaderFfi
    header: SmfHeader
    symbols: Dict<text, SmfSymbol>
    inference_hints: Option<InferenceHints>

    static fn open(path: text) -> Result<SmfReader, SmfError>:
        val ffi = SmfReaderFfi.open(path)?
        val header = SmfHeader.from_raw(ffi.read_header())

        val symbols = ffi.read_symbol_table()
            .map(\s: SmfSymbol.from_raw(s))
            .to_dict(\s: (s.name, s))

        val inference_hints = if header.has_section(SectionType.InferenceHints):
            val data = ffi.read_section(header.inference_hints_index)
            Some(InferenceHints.parse(data))
        else:
            None

        Ok(SmfReader(ffi: ffi, header: header, symbols: symbols, inference_hints: inference_hints))

    fn lookup_symbol(name: text) -> Result<SmfSymbol, SmfError>:
        self.symbols.get(name).ok_or(SmfError.SymbolNotFound(name))

    fn get_inference_hints(symbol: text) -> Option<InferenceHints>:
        self.inference_hints?.for_symbol(symbol)
```

---

## Phase 4: Linker (Simple)

### Goal
Create Simple linker that uses ObjTaker and integrates with mold.

### Tasks

| ID | Task | File | Lang | Est |
|----|------|------|------|-----|
| 4.1 | Create Linker class | `linker/link.spl` | Simple | 2h |
| 4.2 | Implement link() pipeline | `linker/link.spl` | Simple | 4h |
| 4.3 | Implement collect_deferred_hints() | `linker/link.spl` | Simple | 2h |
| 4.4 | Implement resolve_cross_module() | `linker/link.spl` | Simple | 6h |
| 4.5 | Implement take_all_objects() | `linker/link.spl` | Simple | 4h |
| 4.6 | Implement generate_specializations() | `linker/link.spl` | Simple | 4h |
| 4.7 | Implement write_smf() output | `linker/link.spl` | Simple | 4h |
| 4.8 | Create MoldBackend class | `linker/mold.spl` | Simple | 2h |
| 4.9 | Implement mold link() | `linker/mold.spl` | Simple | 4h |
| 4.10 | Implement Rust mold FFI | `linker/mold_ffi.rs` | Rust | 4h |
| 4.11 | Write tests | `test/lib/std/unit/compiler/linker_spec.spl` | Simple | 6h |

### Linker API

```simple
class Linker:
    static fn create() -> Linker

    fn link(inputs: List<text>, output: text, config: LinkConfig) -> Result<(), LinkError>

    # Internal pipeline steps
    fn collect_deferred_hints(readers: List<SmfReader>) -> List<DeferredHint>
    fn resolve_cross_module(hints: List<DeferredHint>, context: LinkContext) -> Result<Dict<DeferredTypeId, Type>, LinkError>
    fn take_all_objects(readers: List<SmfReader>, resolved: Dict<DeferredTypeId, Type>) -> Result<List<ResolvedObject>, LinkError>
    fn generate_specializations(objects: List<ResolvedObject>) -> Result<List<Specialization>, LinkError>

struct LinkConfig:
    output_format: OutputFormat  # Smf | Native
    libraries: List<text>
    pie: bool
    debug: bool

enum OutputFormat:
    Smf      # Runtime SMF
    Native   # ELF/Mach-O via mold
```

### Mold FFI

```rust
// src/rust/compiler/src/linker/mold_ffi.rs

#[no_mangle]
pub extern "C" fn mold_find_path() -> *const c_char {
    // Search for mold in PATH, /usr/bin, etc.
    // Return path or null
}

#[no_mangle]
pub extern "C" fn mold_execute(args: *const *const c_char, argc: usize) -> i32 {
    // Execute mold with args
    // Return exit code
}

#[no_mangle]
pub extern "C" fn write_elf_object(
    code: *const u8,
    code_len: usize,
    symbols: *const SymbolEntry,
    symbol_count: usize,
    output_path: *const c_char,
) -> i32 {
    // Write ELF .o file
    // Return 0 on success
}
```

---

## Phase 5: Loader Integration (Simple)

### Goal
Create Simple module loader using ObjTaker for runtime loading.

### Tasks

| ID | Task | File | Est |
|----|------|------|-----|
| 5.1 | Create ModuleLoader class | `loader/module_loader.spl` | 2h |
| 5.2 | Implement load() method | `loader/module_loader.spl` | 4h |
| 5.3 | Integrate ObjTaker | `loader/module_loader.spl` | 2h |
| 5.4 | Implement runtime instantiation | `loader/instantiate.spl` | 4h |
| 5.5 | Add module cache | `loader/module_loader.spl` | 2h |
| 5.6 | Write tests | `test/lib/std/unit/compiler/loader_spec.spl` | 4h |

### ModuleLoader API

```simple
class ModuleLoader:
    obj_taker: ObjTaker
    loaded: Dict<text, LoadedModule>

    static fn create() -> ModuleLoader

    fn load(path: text) -> Result<LoadedModule, LoadError>
    fn load_symbol(module: text, symbol: text) -> Result<ResolvedObject, LoadError>
    fn instantiate_generic(module: text, symbol: text, type_args: List<Type>) -> Result<ResolvedObject, LoadError>

    fn unload(path: text)
    fn reload(path: text) -> Result<LoadedModule, LoadError>
```

---

## Phase 6: Testing and Documentation

### Tasks

| ID | Task | File | Est |
|----|------|------|-----|
| 6.1 | E2E: compile → link → run | `test/system/features/inference/e2e_spec.spl` | 8h |
| 6.2 | E2E: cross-module generics | `test/system/features/inference/cross_module_spec.spl` | 4h |
| 6.3 | E2E: link-time instantiation | `test/system/features/inference/link_instantiate_spec.spl` | 4h |
| 6.4 | Performance benchmarks | `test/bench/inference_bench.spl` | 4h |
| 6.5 | Update SMF spec | `doc/format/smf_specification.md` | 4h |
| 6.6 | Write migration guide | `doc/guide/inference_migration.md` | 4h |
| 6.7 | Update CLAUDE.md | `CLAUDE.md` | 1h |

### E2E Test Example

```simple
# test/system/features/inference/link_instantiate_spec.spl

describe "Link-Time Instantiation":
    it "instantiates generic at link time":
        # lib.spl defines: fn identity<T>(x: T) -> T: x
        # app.spl uses: identity(42) without type annotation

        # Compile lib.spl
        val lib_smf = compile("test_data/lib.spl")?

        # Compile app.spl
        val app_smf = compile("test_data/app.spl")?

        # Link - should infer T=Int from usage
        val linker = Linker.create()
        linker.link([lib_smf, app_smf], "output.smf", LinkConfig.default())?

        # Verify: output has identity$Int specialization
        val output = SmfReader.open("output.smf")?
        output.lookup_symbol("identity$Int").is_ok().should_be(true)

    it "resolves cross-module type unification":
        # Module A exports: fn process<T>(items: List<T>)
        # Module B imports A, calls process([1, 2, 3])
        # Link should unify T = Int

        val a_smf = compile("test_data/module_a.spl")?
        val b_smf = compile("test_data/module_b.spl")?

        val linker = Linker.create()
        linker.link([a_smf, b_smf], "output.smf", LinkConfig.default())?

        # Check unification happened
        val output = SmfReader.open("output.smf")?
        val hints = output.inference_hints?
        hints.unifications.contains(("A", "B", "T", "Int")).should_be(true)
```

---

## File Summary

| Phase | Simple Files | Rust Files |
|-------|--------------|------------|
| 1. Inference | 7 | 0 |
| 2. ObjTaker | 1 | 0 |
| 3. SMF | 3 | 1 |
| 4. Linker | 2 | 1 |
| 5. Loader | 2 | 0 |
| 6. Tests | 5+ | 0 |
| **Total** | **20+** | **2** |

**Ratio: 90%+ Simple, <10% Rust (FFI only)**

---

## Phase 7: Build simple_new Native Binary

### Goal
Compile `src/app/cli/main.spl` (Simple CLI written in Simple) to native binary using the new Simple linker.

### Tasks

| ID | Task | File | Est |
|----|------|------|-----|
| 7.1 | Compile main.spl to SMF | CLI invocation | 2h |
| 7.2 | Compile all dependencies to SMF | Multiple .spl files | 4h |
| 7.3 | Link SMFs with simple linker | `simple/compiler/linker/` | 4h |
| 7.4 | Generate native binary via mold | `simple_new_native` | 2h |
| 7.5 | Test native binary | Integration tests | 4h |
| 7.6 | Compare with interpreted version | Verification | 2h |
| 7.7 | Update build scripts | `Makefile`, wrappers | 2h |

### Build Pipeline

```
src/app/cli/main.spl
        │
        ▼
┌─────────────────────┐
│  Compile to SMF     │  simple compile main.spl -o cli.smf
│  (with type inference)
└─────────────────────┘
        │
        ▼
┌─────────────────────┐
│  Compile deps       │  simple compile lib/*.spl -o lib/*.smf
└─────────────────────┘
        │
        ▼
┌─────────────────────┐
│  Simple Linker      │  Linker.link([cli.smf, deps...], "simple_new_native")
│  - ObjTaker         │  - Cross-module type inference
│  - Type inference   │  - Generate specializations
│  - Instantiation    │
└─────────────────────┘
        │
        ▼
┌─────────────────────┐
│  Mold Backend       │  mold -o simple_new_native obj_*.o -lc
└─────────────────────┘
        │
        ▼
   simple_new_native   (Native ELF binary)
```

### Expected Output

```bash
# Build simple_new native
$ simple build src/app/cli/main.spl -o simple_new_native --native

# Verify it works
$ ./simple_new_native --version
Simple v0.1.0

$ ./simple_new_native test test/lib/std/unit/
Running 100 tests... OK

# Compare with interpreted
$ ./bin/wrappers/simple_new --version
Simple v0.1.0  # Same output
```

### Success Criteria

| Metric | Target |
|--------|--------|
| Native binary builds | ✅ |
| Functional parity with interpreted | 100% |
| Startup time improvement | >10x faster |
| Binary size | <50MB |
| All CLI commands work | ✅ |

---

## Timeline

| Phase | Duration | Depends On |
|-------|----------|------------|
| Phase 1: Inference | 2 weeks | - |
| Phase 2: ObjTaker | 1 week | Phase 1 |
| Phase 3: SMF | 1 week | Phase 1 |
| Phase 4: Linker | 1.5 weeks | Phase 2, 3 |
| Phase 5: Loader | 1 week | Phase 2 |
| Phase 6: Testing | 1 week | Phase 4, 5 |
| Phase 7: Build simple_new | 1 week | Phase 4, 6 |

**Total: ~8.5 weeks**

---

## Success Criteria

| Metric | Target |
|--------|--------|
| Simple code ratio | >90% |
| Rust FFI functions | <10 |
| Type inference parity | Compiler = Loader = Linker |
| Link-time overhead | <15% |
| Backward compatibility | 100% existing SMF works |

---

## Next Steps

1. Review and approve design
2. Create `simple/compiler/inference/` directory
3. Begin Phase 1: types.spl
4. Set up test infrastructure
