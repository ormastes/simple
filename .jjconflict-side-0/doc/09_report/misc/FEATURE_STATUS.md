# Simple Language - Complete Feature Status

This document consolidates all feature implementation status from `doc/status/*.md` files.

**Last Updated:** 2025-12-17

## Status Legend
- ✅ **COMPLETE** - Fully implemented and tested
- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet implemented
- 🔮 **FUTURE** - Long-term goal
- ❌ **BLOCKED** - Waiting on dependencies

---

## Core Language Features (#1-50)

### #1: Basic Types ✅
**Status:** COMPLETE  
**Implementation:** `src/parser/src/ast.rs`, `src/compiler/src/value.rs`
- Integer types: i8-i64, u8-u64
- Float types: f32, f64
- Boolean, string, nil
- **Coverage:** Parser + runtime value system complete

### #2: String Types ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/collections.rs`
- RuntimeString with UTF-8 support
- String interpolation (f-strings)
- FFI functions: `rt_string_*`

### #3: Mutability Control ✅
**Status:** COMPLETE  
**Implementation:** `src/parser/src/ast.rs`, MIR effects
- `let` (immutable) vs `let mut` (mutable)
- Effect tracking in MIR
- Formal verification: `src/verification/nogc_compile/`

### #4: Variables & Let Bindings ✅
**Status:** COMPLETE  
**Implementation:** Parser, interpreter, codegen
- Pattern destructuring in let bindings
- Type inference integration

### #5: Control Flow (if/elif/else) ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/interpreter_control.rs`
- Conditional expressions
- Block-based syntax

### #6: Loops (for/while/loop/break/continue) ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/interpreter_control.rs`
- Iterator-based for loops
- While loops with conditions
- Infinite loops with break/continue

### #7: Functions ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/interpreter_call.rs`
- Named functions
- Return values
- Default arguments
- FFI: `rt_closure_*` functions

### #8: Indentation-Based Blocks ✅
**Status:** COMPLETE  
**Implementation:** `src/parser/src/lexer/indentation.rs`
- INDENT/DEDENT token tracking
- Whitespace-sensitive parsing

### #9: Structs ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/objects.rs`
- Field access via MIR FieldGet/FieldSet
- Struct initialization
- FFI: `rt_struct_*` functions

### #10: Classes & Methods ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/objects.rs`
- Method dispatch
- Self parameter binding
- Inheritance (basic)

### #11: Enums ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/objects.rs`
- Discriminant tracking
- Variant data storage
- Pattern matching integration
- FFI: `rt_enum_*` functions

### #12: Pattern Matching ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/interpreter_control.rs`, `src/compiler/src/mir/types.rs`
- Match expressions with all pattern types
- Pattern types: literal (int/bool/string), bind, wildcard, struct, tuple, array, enum (single and multi-payload), range, or-patterns, guards
- `if-let` pattern matching
- MIR instructions: PatternTest, PatternBind
- **BDD Tests:** 79 passing (`simple/std_lib/test/unit/compiler_core/pattern_matching_spec.spl`)

### #13: Type Inference 🔄
**Status:** IN PROGRESS  
**Implementation:** `src/type/src/lib.rs`
- Hindley-Milner scaffold complete
- Unification, generalize, instantiate
- **Next:** Full AST integration

### #14: Generics ✅
**Status:** COMPLETE (monomorphization)  
**Implementation:** `src/compiler/src/monomorphize/`
- Type parameter substitution
- Constraint checking
- Specialization for concrete types

### #15: Traits ✅
**Status:** COMPLETE
**Implementation:** Parser + interpreter complete
- Trait definitions parsed
- Impl blocks supported
- Associated types ✅ (parser complete, 5 tests)
- Dynamic dispatch via TraitObject ✅ (4 tests)
- Coercion in let bindings and function parameters

### #16: Impl Blocks ✅
**Status:** COMPLETE  
**Implementation:** Parser + interpreter
- Method definitions
- Associated functions

### #17: Lambdas/Closures ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/objects.rs`
- Capture environment
- MIR: ClosureCreate, IndirectCall
- FFI: `rt_closure_create`, `rt_closure_call`

### #18: Named Arguments ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/expressions/mod.rs`
- Syntax: `func(name: value)`
- Parser: Named argument detection in call expressions
- Interpreter: Named argument handling

### #19: Trailing Blocks ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/expressions/mod.rs`
- Ruby-style block passing
- Parser: Block arguments after function calls

### #20: Functional Update Operator ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/expressions/mod.rs`
- Syntax: `new_struct = old_struct { field: new_value }`
- Parser and interpreter support

### #21: String Interpolation ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/mir/types.rs`
- MIR: FStringFormat instruction
- Runtime formatting via FFI

### #22: Comments ✅
**Status:** COMPLETE  
**Implementation:** `src/parser/src/lexer/comments.rs`
- Single-line `#`
- Multi-line `###...###`
- Doc comments `##`

### #23: Line Continuation ✅
**Status:** COMPLETE  
**Implementation:** Lexer
- Backslash continuation `\`
- Implicit continuation in brackets

### #24: GC-Managed Memory ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/memory/gc.rs`
- Abfall integration
- Optional logging (`--gc-log`)
- Default for all heap types

### #25: Unique Pointers ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/value_pointers.rs`, `src/common/src/manual_mem.rs`
- Syntax: `new & value` creates unique pointer
- RAII semantics with automatic drop at scope exit
- Move semantics enforcement (use-after-move detection)
- Runtime FFI: `rt_unique_*` functions
- **Tests:** `interpreter_memory.rs` (24 tests)

### #26: Shared Pointers ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/value_pointers.rs`, `src/common/src/manual_mem.rs`
- Syntax: `new * value` creates shared pointer
- Reference counting with automatic cleanup
- Clone on assignment (refcount++)
- Runtime FFI: `rt_shared_*` functions

### #27: Weak Pointers ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/value_pointers.rs`, `src/common/src/manual_mem.rs`
- Syntax: `new - value` creates weak pointer
- Weak reference semantics (doesn't prevent drop)
- Upgrade to shared pointer when accessed
- Runtime FFI: `rt_weak_*` functions

### #28: Handle Pointers ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/value_pointers.rs`, `src/common/src/manual_mem.rs`
- Syntax: `new + value` creates handle pointer
- `handle_pool T: capacity: N` declaration syntax
- Pool-based allocation with generation tracking
- Runtime FFI: `rt_handle_*` functions

### #29: Borrowing ✅
**Status:** COMPLETE (effect tracking)  
**Implementation:** `src/compiler/src/effects.rs`
- Immutable borrows tracked
- Mutable borrow exclusivity
- Formal verification: `src/verification/manual_pointer_borrow/`

### #30: Actors ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/actors.rs`
- Spawn, send, receive
- MIR: ActorSpawn, ActorSend, ActorRecv
- FFI: `rt_actor_spawn`, `rt_actor_send`, `rt_actor_recv`
- **Note:** Body outlining uses stub (Feature #99 pending)

### #31: Concurrency Primitives ✅
**Status:** COMPLETE
**Implementation:** `src/runtime/src/value/sync.rs`
- RuntimeMutex: `rt_mutex_new`, `rt_mutex_lock`, `rt_mutex_try_lock`, `rt_mutex_unlock`, `rt_mutex_free`
- RuntimeRwLock: `rt_rwlock_new`, `rt_rwlock_read`, `rt_rwlock_write`, `rt_rwlock_set`, `rt_rwlock_free`
- RuntimeSemaphore: `rt_semaphore_new`, `rt_semaphore_acquire`, `rt_semaphore_release`, `rt_semaphore_free`
- RuntimeBarrier: `rt_barrier_new`, `rt_barrier_wait`, `rt_barrier_free`
- HeapObjectType variants: Mutex, RwLock, Semaphore, Barrier

### #32: Async Effects ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/effects.rs`
- Async function tracking
- Effect propagation
- MIR effect annotations
- Formal verification: `src/verification/async_compile/`

### #33: Stackless Coroutine Actors ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/mir/generator.rs`
- Generator state machine lowering
- MIR: GeneratorCreate, Yield, GeneratorNext
- FFI: `rt_generator_*` functions
- **Note:** Body outlining uses stub (Feature #99 pending)

### #34: Macros ✅
**Status:** COMPLETE (expansion)  
**Implementation:** `src/compiler/src/interpreter_macro.rs`
- Quote/unquote
- AST rewriting
- Hygiene (basic)

### #35: Context Blocks ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/interpreter.rs`
- `context expr:` block syntax
- Implicit method dispatch to context object
- Thread-local `CONTEXT_OBJECT` for dispatch

### #36: Method Missing ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/interpreter_method.rs`
- `method_missing(self, name, args, block)` handler
- Dynamic method dispatch when method not found
- Works with context blocks

### #37: Union Types 📋
**Status:** DESIGN REQUIRED
**Implementation:** Not started
**Design:** See `doc/05_design/type_system_features.md`
- Tagged unions (algebraic data types)
- Syntax: `union Shape: Circle(r: f64) | Rectangle(w: f64, h: f64)`
- Pattern matching integration
- Variant constructors
- **Blocked:** Type system design

### #37b: Result Type 📋
**Status:** DESIGN REQUIRED
**Implementation:** Not started (depends on #37)
**Design:** See `doc/05_design/type_system_features.md`
- `Result[T, E]` = `Ok(T) | Err(E)`
- `?` operator for error propagation
- `unwrap()`, `map()`, `and_then()` methods

### #37c: Bitfields 📋
**Status:** DESIGN REQUIRED
**Implementation:** Not started
**Design:** See `doc/05_design/type_system_features.md`
- Packed bit-level structs
- Syntax: `bitfield Flags(u8): readable: 1, writable: 1`
- Hardware register access, FFI compatibility

### #38: Option Type ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/value.rs`
- Value::Nil for None
- Pattern matching support
- MIR: OptionSome, OptionUnwrap

### #39: Symbols/Atoms ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/mir/types.rs`
- MIR: ConstSymbol instruction
- Interned symbol table

### #40: Tuple Types ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/collections.rs`
- Heterogeneous element types
- MIR: TupleLit
- FFI: `rt_tuple_*` functions

### #41: Array Types ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/collections.rs`
- Dynamic arrays
- MIR: ArrayLit, IndexGet, IndexSet
- FFI: `rt_array_*` functions

### #42: Dictionary Types ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/collections.rs`
- Hash map implementation
- MIR: DictLit
- FFI: `rt_dict_*` functions

### #43: Type Aliases ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/statements/mod.rs`
- Parser: `parse_type_alias()` → `Node::TypeAlias(TypeAliasDef)`
- Syntax: `type Name = Type`, `pub type Name = Type`
- Supports simple types, generic types, function types
- Test: `interpreter_type_alias`

### #44: Visibility Modifiers ✅
**Status:** COMPLETE (Parser)
**Implementation:** `src/parser/src/ast/enums.rs`
- `pub`, `priv` keywords
- `Visibility` enum on AST nodes
- Note: Runtime enforcement pending (#99)

### #45: Static/Const Declarations ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/statements/mod.rs`
- `const NAME = value` (compile-time constants, immutable)
- `static NAME = value` (global, immutable by default)
- `static mut NAME = value` (global, mutable)
- Type annotations optional, `pub` visibility supported

### #46: Extern Functions (FFI) ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/interpreter_extern.rs`
- C ABI bindings
- Dynamic library loading
- Type marshalling

### #47: No-Parentheses Calls ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/expressions/mod.rs`
- Ruby-style syntax at statement level
- Parser handles ambiguity resolution

### #48: Futures and Promises ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/async_gen.rs`
- MIR: FutureCreate, Await
- FFI: `rt_future_*` functions
- **Note:** Body outlining uses stub (Feature #99 pending)

### #49: Arithmetic Operators ✅
**Status:** COMPLETE  
**Implementation:** MIR BinOp instruction
- +, -, *, /, %, **
- Integer and float support

### #50: Comparison Operators ✅
**Status:** COMPLETE  
**Implementation:** MIR BinOp instruction
- ==, !=, <, <=, >, >=
- Type-aware comparisons

---

## Codegen Features (#99-103)

### #99: Body Block Outlining ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/codegen/shared.rs`
- `expand_with_outlined()` extracts actor/generator/future bodies
- `create_outlined_function()` creates separate MirFunction for each body_block
- Live-in analysis and capture buffer support
- Used by both AOT and JIT backends

### #100: Capture Buffer & VReg Remapping ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/codegen/cranelift.rs`
- Capture struct generation
- Virtual register mapping
- **Dependency:** Feature #99 (outlining)

### #101: Generator State Machine Codegen ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/mir/generator.rs`
- State enum generation
- Yield point lowering
- Resume logic

### #102: Future Body Execution 🔄
**Status:** IN PROGRESS
**Implementation:** `src/runtime/src/value/async_gen.rs`
- Eager execution implemented
- Full async/await state machine pending
- **Dependency:** Feature #99 complete, unblocked

### #103: Codegen Parity Completion 🔄
**Status:** IN PROGRESS
**Implementation:** Multiple codegen modules
- Native codegen handles most MIR instructions
- 50+ FFI functions defined in `runtime_ffi.rs`
- `compilability.rs` analysis exists but not integrated
- `InterpCall`/`InterpEval` defined but not emitted
- **Next:** Integrate hybrid execution (see `doc/status/codegen_parity_completion.md`)

---

## Extended Features (#200-220)

### #200-209: Unit Types ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/statements/mod.rs`, `src/compiler/src/interpreter.rs`
- Standalone units: `unit Bytes: i64 as bytes`
- Unit families: `unit_family Time: ns, us, ms, s`
- Compound units: `unit Speed = Distance / Time`
- Type-safe unit arithmetic (#203)
- Unit inference (#208), assertions (#209)
- String suffixes: `100ms`, `1024bytes`

### #210-215: Networking APIs ✅
**Status:** COMPLETE (Runtime FFI)
**Implementation:** `src/runtime/src/value/net.rs`
- TCP: bind, accept, connect, read, write, flush, shutdown, close
- UDP: bind, connect, recv, send, recv_from, send_to
- HTTP: basic client support
- Socket options: nodelay, keepalive, timeouts, broadcast
- ~50+ FFI functions implemented

### #220: LLVM Backend ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/codegen/llvm.rs`
- LLVM IR generation
- Optimization passes
- Native code emission

---

## Testing Features (#300-303)

### #300: BDD Spec Framework ✅
**Status:** COMPLETE  
**Implementation:** `simple/std_lib/src/tools/spec.spl`
- describe/it/expect DSL
- Assertion library
- Test runner integration
- **Coverage:** Sprint 1 complete

### #301: Doctest ✅
**Status:** COMPLETE  
**Implementation:** `doc/status/sdoctest.md`
- Extract code from doc comments
- Execute and verify output
- **Coverage:** Sprint 2 complete

### #302: Test CLI Integration ✅
**Status:** COMPLETE
**Implementation:** `src/driver/src/cli/test_runner.rs`
- `simple test [path]` command
- Test levels: --unit, --integration, --system
- Output formats: text, json, doc
- Options: --tag, --fail-fast, --seed

### #303: JJ Version Control 🔄
**Status:** IN PROGRESS (67%)  
**Implementation:** `doc/plans/27_jj_integration.md`
- Repository operations (8/12 tasks)
- Change-based workflow
- **Next:** Advanced features

---

## Advanced Features (#400-536)

### #400-405: Contract Blocks 🔄
**Status:** IN PROGRESS (MIR complete, parser incomplete)
**Implementation:** `src/compiler/src/mir/lower.rs`, `src/parser/src/statements/contract.rs`
- Preconditions: `in:` blocks
- Postconditions: `out(ret):` and `out_err(err):` blocks
- Invariants: `invariant:` blocks
- Old value capture: `old()` expressions
- MIR: ContractCheck, ContractOldCapture
- Contract modes: Off, Boundary, All, Test
- **Blocked:** Parser doesn't recognize contract syntax (10 tests failing)

### #410-415: Capability-Based Imports ✅
**Status:** COMPLETE
**Implementation:** `src/parser/src/ast/nodes.rs`, `src/compiler/src/module_resolver.rs`
- Capabilities: Pure, Io, Net, Fs, Unsafe, Gc
- `requires [pure, io]` module declarations
- Effect-to-capability validation
- Capability inheritance enforcement
- Tests in `effects_tests.rs`

### #510-512: UI Framework 📋
**Status:** PLANNED  
**Implementation:** Design phase
- .sui file format (structural UI)
- Dynamic structure (#510)
- Structural PatchSet (#511)
- SSR + Hydration (#512)
- GUI/TUI renderers

### #520-536: Web Framework 📋
**Status:** PLANNED  
**Implementation:** Design phase
- Controllers, views, models
- Routing, middleware
- WASM client build
- Server-side rendering

### GPU & SIMD (#400-418) 🔄
**Status:** IN PROGRESS (8/19 features in progress)
**Spec:** `doc/06_spec/gpu_simd/README.md` (updated 2025-12)
**Implementation:** `src/compiler/src/codegen/llvm/gpu.rs`, `src/runtime/src/value/gpu.rs`

#### Core Infrastructure (Complete)
- ✅ GPU MIR instructions (GpuGlobalId, GpuLocalId, GpuGroupId, GpuBarrier, GpuAtomic, etc.)
- ✅ Software backend for CPU-based kernel execution
- ✅ LLVM GPU backend for NVPTX/PTX generation (SM50-SM90)
- ✅ CUDA runtime wrapper (device enum, context, module loading)
- ✅ GPU FFI functions (30+ functions)

#### SIMD Features (#400-404)
| ID | Feature | Status |
|----|---------|--------|
| #400 | SIMD vectors (`vec[N, T]`) | 🔄 MIR support, codegen pending |
| #401 | Vector arithmetic (lane-wise ops) | 🔄 MIR support |
| #402 | Lane operations (shuffle, swizzle) | 📋 Planned |
| #403 | Reduction ops (sum, min, max) | 📋 Planned |
| #404 | Mask operations (select, gather/scatter) | 📋 Planned |

#### GPU Kernel Features (#405-410)
| ID | Feature | Status |
|----|---------|--------|
| #405 | GPU kernels (`#[gpu]`, `@simd`) | 🔄 Basic support, attribute parsing pending |
| #406 | Thread blocks (grid/block dims) | 🔄 MIR support complete |
| #407 | Shared memory (`shared let`) | 🔄 MIR GpuSharedAlloc complete |
| #408 | Synchronization (barriers, fences) | 🔄 GpuBarrier, GpuMemFence complete |
| #409 | Atomic operations | 🔄 GpuAtomic complete (9 ops) |
| #410 | GPU device API (context, buffers) | 🔄 CUDA runtime wrapper |

#### Safety & Convenience Features (#411-418)
| ID | Feature | Status |
|----|---------|--------|
| #411 | Bounds policy (`@bounds(...)`) | 📋 Spec complete |
| #412 | `bounds:` clause (pattern handlers) | 📋 Spec complete |
| #413 | Indexer trait (user-defined `[]`) | 📋 Spec complete |
| #414 | Neighbor accessors (`.left_neighbor`) | 📋 Spec complete |
| #415 | Parallel iterators (`par_map`, etc.) | 📋 Spec complete |
| #416 | Tensor operations (`@` operator) | 📋 Preview spec |
| #417 | Hardware detection | 📋 Spec complete |
| #418 | Async GPU operations | 📋 Spec complete |

**See:** `doc/llvm_backend.md` for backend details, `doc/06_spec/gpu_simd/README.md` for full spec

---

## Infrastructure Features

### Package Manager ✅
**Status:** COMPLETE  
**Implementation:** `src/pkg/`
- UV-style dependency resolution
- simple.toml manifest
- simple.lock lockfile
- Global cache with hard links
- Commands: init, add, install, update, list, cache

### Module System ✅
**Status:** COMPLETE
**Implementation:** `src/compiler/src/module_resolver.rs`, `src/dependency_tracker/`
- Parsing: ✅ Complete
- Path resolution: ✅ Complete
- __init__.spl: ✅ Complete
- Import dependency graph: ✅ Complete (38 tests passing)
- Cycle detection: ✅ Complete
- Visibility rules: ✅ Complete
- Symbol resolution: ✅ Complete

### Interpreter Interface ✅
**Status:** COMPLETE  
**Implementation:** `src/driver/src/interpreter.rs`
- High-level API with I/O capture
- Integration with runner
- Dependency caching

### Code Quality Tools ✅
**Status:** COMPLETE  
**Implementation:** Makefile, CI scripts
- cargo-llvm-cov: 631+ tests
- jscpd: Duplication detection
- Clippy: Linting
- rustfmt: Code formatting

### Formal Verification ✅
**Status:** COMPLETE (models)  
**Implementation:** `src/verification/`
- Borrow checker model
- GC safety model
- Effect tracking model
- Type inference model
- **Coverage:** 5 Lean 4 projects

---

## Summary Statistics

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 47 | 45 | 1 | 1 |
| Codegen | 5 | 4 | 1 | 0 |
| Testing & CLI | 4 | 4 | 0 | 0 |
| Concurrency Runtime | 4 | 4 | 0 | 0 |
| Contracts | 6 | 0 | 6 | 0 |
| Extended - Units | 10 | 10 | 0 | 0 |
| Extended - Networking | 6 | 6 | 0 | 0 |
| Advanced - Effects | 6 | 6 | 0 | 0 |
| Advanced - UI | 3 | 0 | 0 | 3 |
| Advanced - Web | 17 | 0 | 0 | 17 |
| Advanced - GPU/SIMD | 19 | 5 | 8 | 6 |
| **TOTAL** | **127** | **84** | **16** | **27** |

**Overall Progress:** 66% (84/127 complete, 16 in progress)

---

## Recent Work (2025-12-17)

### Interpreter Enhancements
- **String methods added:** `find_str`, `trimmed`, `sorted`, `taken`, `dropped`, `appended`, `prepended`, `push`, `push_str`, `pop`, `clear`
- **Option methods added:** `or`, `ok_or`
- **Result method added:** `or`
- **BDD framework:** Added `skip` builtin for skipped tests

### Test Status
- **Simple stdlib tests:** 24 passed, 0 failed
- **Driver tests:** 700+ passed, 0 failed
- **Compiler tests:** 322 passed, 10 failed (contract parser)
- **Total:** ~1046+ tests passing

---

## Next Priorities

### Immediate (Sprint)
1. **Contract parser support** - Add `in:`, `out:`, `invariant:` syntax to parser (10 tests blocked)
2. **Collection mutation** - Array/List/Dict mutation doesn't persist changes
3. **Type annotation scope bug** - Variables become inaccessible after type-annotated let

### Short Term (Month)
1. Union types (#37) - Tagged union syntax and pattern matching
2. Result type (#37b) - `Result[T, E]` with `?` operator
3. Full type inference (#13) - AST integration

### Medium Term (Quarter)
1. GPU kernel features (#405-410) - complete MIR-to-codegen path
2. SIMD operations (#400-404) - CPU vector support
3. Doctest framework - List mutation and Set support needed
4. UI framework prototype (#510-512)
5. Web framework basics (#520-536)

---

**See Also:**
- [Feature Index](feature_index.md) - Categorized feature list
- [Codegen Status](codegen_status.md) - MIR instruction coverage
- Individual status files: `doc/status/*.md`
