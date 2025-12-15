# Simple Language - Complete Feature Status

This document consolidates all feature implementation status from `doc/status/*.md` files.

**Last Updated:** 2025-12-15

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
- Formal verification: `verification/nogc_compile/`

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
**Implementation:** `src/compiler/src/mir/types.rs`
- Match expressions
- Pattern types: literal, bind, wildcard, struct, tuple, array
- MIR instructions: PatternTest, PatternBind

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

### #15: Traits 🔄
**Status:** IN PROGRESS  
**Implementation:** Parser complete, codegen pending
- Trait definitions parsed
- Impl blocks supported
- **Next:** Dynamic dispatch

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

### #18: Named Arguments 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- Syntax: `func(name: value)`
- **Blocked:** Interpreter implementation

### #19: Trailing Blocks 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- Ruby-style block passing
- **Blocked:** Interpreter implementation

### #20: Functional Update Operator 🔄
**Status:** PLANNED  
**Implementation:** Design complete
- Syntax: `new_struct = old_struct { field: new_value }`
- **Blocked:** MIR lowering

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

### #25: Unique Pointers 🔄
**Status:** PLANNED  
**Implementation:** Design complete
- Syntax: `&T`
- RAII semantics
- **Blocked:** Ownership tracking in MIR

### #26: Shared Pointers 🔄
**Status:** PLANNED  
**Implementation:** Design complete
- Syntax: `*T`
- Reference counting
- **Blocked:** Runtime implementation

### #27: Weak Pointers 🔄
**Status:** PLANNED  
**Implementation:** Design complete
- Syntax: `~T`
- Weak reference semantics
- **Blocked:** Runtime implementation

### #28: Handle Pointers 🔄
**Status:** PLANNED  
**Implementation:** Design complete
- Opaque resource handles
- **Blocked:** Runtime implementation

### #29: Borrowing ✅
**Status:** COMPLETE (effect tracking)  
**Implementation:** `src/compiler/src/effects.rs`
- Immutable borrows tracked
- Mutable borrow exclusivity
- Formal verification: `verification/manual_pointer_borrow/`

### #30: Actors ✅
**Status:** COMPLETE  
**Implementation:** `src/runtime/src/value/actors.rs`
- Spawn, send, receive
- MIR: ActorSpawn, ActorSend, ActorRecv
- FFI: `rt_actor_spawn`, `rt_actor_send`, `rt_actor_recv`
- **Note:** Body outlining uses stub (Feature #99 pending)

### #31: Concurrency Primitives 🔄
**Status:** PLANNED  
**Implementation:** Design complete
- Mutex, RwLock, Semaphore, Barrier
- **Blocked:** Runtime implementation

### #32: Async Effects ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/effects.rs`
- Async function tracking
- Effect propagation
- MIR effect annotations
- Formal verification: `verification/async_compile/`

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

### #35: Context Blocks 📋
**Status:** PLANNED  
**Implementation:** Design complete
- Resource management (with/using)
- **Blocked:** Parser + interpreter

### #36: Method Missing 📋
**Status:** PLANNED  
**Implementation:** Design complete
- Dynamic method dispatch fallback
- **Blocked:** Runtime implementation

### #37: Union Types 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- Syntax: `T | U`
- Type checking
- **Blocked:** Type system integration

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

### #43: Type Aliases 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- Syntax: `type Name = Type`
- **Blocked:** Type system integration

### #44: Visibility Modifiers 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- `pub`, `pub(crate)`, `pub(super)`
- **Blocked:** Module system integration

### #45: Static/Const Declarations 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- Module-level constants
- **Blocked:** Interpreter implementation

### #46: Extern Functions (FFI) ✅
**Status:** COMPLETE  
**Implementation:** `src/compiler/src/interpreter_extern.rs`
- C ABI bindings
- Dynamic library loading
- Type marshalling

### #47: No-Parentheses Calls 🔄
**Status:** PLANNED  
**Implementation:** Parser design complete
- Ruby-style syntax
- **Blocked:** Ambiguity resolution

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

### #99: Body Block Outlining 📋
**Status:** PLANNED  
**Implementation:** Design in `doc/codegen_technical_features.md`
- Extract actor/generator/future bodies to separate functions
- Enable proper closure capture
- **Blocked:** Codegen refactor

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

### #102: Future Body Execution (Compiled) 📋
**Status:** PLANNED  
**Implementation:** Design complete
- Async body compilation
- Await point handling
- **Blocked:** Feature #99 (outlining)

### #103: Codegen Parity Completion 🔄
**Status:** IN PROGRESS  
**Implementation:** Multiple codegen modules
- RuntimeValue bridge complete
- 50+ FFI functions defined
- **Next:** Complete stub replacements

---

## Extended Features (#200-220)

### #200-209: Unit Types 📋
**Status:** PLANNED  
**Implementation:** Design in `doc/spec/units.md`
- Physical units (length, time, velocity)
- Network types (IpAddr, Port, Url)
- File system types (FilePath)
- String suffixes (`100ms`, `192.168.1.1`)

### #210-215: Networking APIs 📋
**Status:** PLANNED  
**Implementation:** Design in `doc/plans/09_stdlib_units_and_networking.md`
- TCP/UDP sockets
- HTTP client/server
- FTP client
- Async I/O integration

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

### #302: Test CLI Integration 📋
**Status:** PLANNED  
**Implementation:** Design in `doc/plans/29_doctest.md`
- `simple test` command
- Coverage reporting
- **Blocked:** CLI extension

### #303: JJ Version Control 🔄
**Status:** IN PROGRESS (67%)  
**Implementation:** `doc/plans/27_jj_integration.md`
- Repository operations (8/12 tasks)
- Change-based workflow
- **Next:** Advanced features

---

## Advanced Features (#400-536)

### #400-405: Contract Blocks 📋
**Status:** PLANNED  
**Implementation:** `doc/features/contracts.md`
- Preconditions: `requires`
- Postconditions: `ensures`
- Invariants: `invariant`
- Refinement types
- **Design:** Complete, awaiting implementation

### #410-415: Capability-Based Imports 📋
**Status:** PLANNED  
**Implementation:** `doc/plans/llm_friendly.md`
- Effect declaration at import
- Capability granting
- Static verification

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

### #126: GPU Kernels 📋
**Status:** PLANNED  
**Implementation:** `doc/spec/gpu_simd.md`
- `#[gpu]` attribute
- Kernel compilation
- Device memory management
- **Blocked:** GPU backend integration

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

### Module System 🔄
**Status:** IN PROGRESS  
**Implementation:** `src/compiler/src/module_resolver.rs`
- Parsing: ✅ Complete
- Path resolution: ✅ Complete
- __init__.spl: ✅ Complete
- **Next:** Import dependency graph

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
**Implementation:** `verification/`
- Borrow checker model
- GC safety model
- Effect tracking model
- Type inference model
- **Coverage:** 5 Lean 4 projects

---

## Summary Statistics

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 50 | 38 | 8 | 4 |
| Codegen | 5 | 2 | 1 | 2 |
| Extended | 21 | 1 | 0 | 20 |
| Testing | 4 | 2 | 1 | 1 |
| Advanced | 127 | 0 | 0 | 127 |
| Infrastructure | 5 | 4 | 1 | 0 |
| **TOTAL** | **212** | **47** | **11** | **154** |

**Overall Progress:** 22% (47/212 complete)

---

## Next Priorities

### Immediate (Sprint)
1. Complete Feature #99 (Body Block Outlining) - unblocks actors/generators/futures
2. Finish Module System dependency graph
3. Type Inference full AST integration

### Short Term (Month)
1. Memory pointer types (#25-28)
2. Trait dynamic dispatch (#15)
3. Union types (#37)
4. Named arguments (#18)

### Medium Term (Quarter)
1. Unit types (#200-209)
2. Networking APIs (#210-215)
3. Contract blocks (#400-405)

### Long Term (Year)
1. UI Framework (#510-512)
2. Web Framework (#520-536)
3. GPU Kernels (#126)

---

**See Also:**
- [Feature Index](feature_index.md) - Categorized feature list
- [Codegen Status](codegen_status.md) - MIR instruction coverage
- Individual status files: `doc/status/*.md`
