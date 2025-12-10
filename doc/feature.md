# Simple Language Features

## Feature List with Ratings

| # | Feature | Importance (1-5) | Difficulty (1-5) | Architecture Impact |
|---|---------|------------------|------------------|---------------------|
| 1 | **Basic Types** (i8-i64, u8-u64, f32-f64, bool, str, nil) | 5 | 1 | Lexer, Parser, Type System, Codegen |
| 2 | **Variables & Let Bindings** | 5 | 2 | Parser, Semantic Analysis, Codegen |
| 3 | **Mutability Control** (mut/immut keywords) | 4 | 3 | Parser, Type System, Semantic Analysis |
| 4 | **Operators** (arithmetic, comparison, logical, bitwise) | 5 | 2 | Lexer, Parser, Codegen |
| 5 | **Control Flow** (if/else/elif) | 5 | 2 | Parser, Codegen |
| 6 | **Loops** (for, while, loop, break, continue) | 5 | 2 | Parser, Codegen |
| 7 | **Functions** (fn, parameters, return types) | 5 | 3 | Parser, Type System, Codegen, Runtime |
| 8 | **Indentation-Based Blocks** | 4 | 4 | Lexer (External Scanner), Parser |
| 9 | **Structs** (value types, fields) | 5 | 3 | Parser, Type System, Memory Layout, Codegen |
| 10 | **Classes** (reference types, methods) | 4 | 4 | Parser, Type System, Memory, GC, Codegen |
| 11 | **Enums** (algebraic data types, variants) | 5 | 3 | Parser, Type System, Pattern Matching, Codegen |
| 12 | **Pattern Matching** (match/case, destructuring) | 5 | 4 | Parser, Type System, Exhaustiveness Check, Codegen |
| 13 | **Type Inference** | 4 | 5 | Type System (Hindley-Milner or similar) |
| 14 | **Generics/Type Parameters** | 4 | 5 | Parser, Type System, Monomorphization/Codegen |
| 15 | **Traits** (interfaces, polymorphism) | 4 | 4 | Parser, Type System, Vtables/Codegen |
| 16 | **Impl Blocks** | 4 | 3 | Parser, Type System, Method Resolution |
| 17 | **Lambdas/Closures** (\x: expr syntax) | 4 | 4 | Parser, Type System, Closure Capture, Codegen |
| 18 | **Named Arguments** | 3 | 2 | Parser, Codegen |
| 19 | **Trailing Blocks** | 3 | 3 | Parser, Lambda Integration |
| 20 | **Functional Update Operator** (->) | 3 | 2 | Parser, Desugaring |
| 21 | **String Interpolation** ({expr} in strings) | 3 | 3 | Lexer, Parser, Codegen |
| 22 | **Comments** (# line comments) | 5 | 1 | Lexer |
| 23 | **Line Continuation** (\ at end of line) | 2 | 2 | Lexer |
| 24 | **GC-Managed Memory** (default T) | 5 | 5 | Runtime, GC Implementation, Codegen |
| 25 | **Unique Pointers** (&T, RAII) | 4 | 4 | Type System, Borrow Checking, Codegen |
| 26 | **Shared Pointers** (*T, refcounting) | 4 | 4 | Runtime, Type System, Codegen |
| 27 | **Weak Pointers** (-T) | 3 | 3 | Runtime, Type System |
| 28 | **Handle Pointers** (+T, handle pools) | 3 | 4 | Runtime, Type System, Pool Management |
| 29 | **Borrowing** (&T_borrow, &mut T_borrow) | 4 | 5 | Type System, Borrow Checker |
| 30 | **Actors** (actor keyword, state, message handlers) | 4 | 5 | Parser, Type System, Runtime Scheduler |
| 31 | **Concurrency Primitives** (spawn, send, receive) | 4 | 5 | Runtime, Scheduler, Message Queues |
| 32 | **Async Effects** | 3 | 5 | Type System, Effect Analysis, Runtime Guards |
| 33 | **Stackless Coroutine Actors** | 3 | 5 | Runtime, State Machine Transform |
| 34 | **Macros** (compile-time code generation) | 3 | 5 | Macro System, AST Manipulation, Hygiene |
| 35 | **Context Blocks** (DSL support) | 2 | 3 | Parser, Scope Resolution |
| 36 | **Method Missing** (dynamic dispatch) | 2 | 4 | Runtime, Dynamic Dispatch |
| 37 | **Union Types** (A | B inline unions) | 3 | 4 | Type System, Codegen |
| 38 | **Option Type** (T?) | 4 | 2 | Type System (sugar for enum) |
| 39 | **Symbols/Atoms** (:symbol) | 2 | 2 | Lexer, Interning, Type System |
| 40 | **Tuple Types** | 4 | 2 | Parser, Type System, Codegen |
| 41 | **Array Types** ([T], [T; N]) | 5 | 3 | Parser, Type System, Bounds Check, Codegen |
| 42 | **Dictionary Types** ({K: V}) | 4 | 3 | Parser, Type System, Runtime (Hash) |
| 43 | **Type Aliases** (type X = Y) | 3 | 2 | Parser, Type System |
| 44 | **Visibility Modifiers** (pub, priv) | 3 | 2 | Parser, Semantic Analysis |
| 45 | **Static/Const Declarations** | 4 | 3 | Parser, Semantic Analysis, Codegen |
| 46 | **Extern Functions** (FFI) | 3 | 4 | Parser, Codegen, Linking |
| 47 | **No-Parentheses Calls** (statement level) | 2 | 3 | Parser (careful grammar design) |
| 48 | **Futures and Promises** (async/await, combinators) | 4 | 4 | Parser, Type System, Runtime (Executor), Codegen |
| 49 | **Compiler SMF Generation** (compile source to .smf binary) | 5 | 2 | Compiler, Pipeline, SMF Writer |
| 50 | **Runner SMF Execution** (run .spl source or .smf binary) | 5 | 2 | Driver, Loader, Runner |
| 51 | **Interpreter In-Memory Binary** (compile to BMF in memory, load and run) | 4 | 3 | Compiler, Loader, Interpreter, Memory |
| 52 | **Unified CLI** (`simple` command like Python/Java) | 5 | 2 | Driver, CLI |
| 53 | **Interactive REPL** (`simple` with no args, like Python) | 4 | 3 | Driver, Interpreter, CLI |
| 54 | **Watch Mode** (`simple watch` for auto-compile on change) | 3 | 3 | Driver, Watcher, CLI |
| 55 | **Run Expression** (`simple -c "expr"` like Python) | 4 | 2 | Driver, Interpreter, CLI |
| 56 | **Package Manager Core** (UV-style fast package management) | 5 | 4 | Driver, Network, Cache, Resolver |
| 57 | **Git Registry** (GitHub folder as package index) | 5 | 3 | Package Manager, Git |
| 58 | **Registry Server** (HTTP API for package registry) | 3 | 4 | Package Manager, Server |
| 59 | **Dependency Resolution** (PubGrub algorithm, parallel) | 5 | 4 | Package Manager, Resolver |
| 60 | **Global Cache** (shared cache with hard links) | 4 | 3 | Package Manager, Cache |
| 61 | **Lock File** (reproducible builds with simple.lock) | 5 | 2 | Package Manager |
| 62 | **List Comprehension** (`[x*2 for x in items]`) | 5 | 3 | Parser, Codegen |
| 63 | **Dict Comprehension** (`{k: v for k,v in pairs}`) | 4 | 3 | Parser, Codegen |
| 64 | **Slicing** (`items[1:3]`, `items[::2]`, `items[::-1]`) | 5 | 3 | Parser, Runtime |
| 65 | **Negative Indexing** (`items[-1]` for last element) | 5 | 2 | Parser, Runtime |
| 66 | **Tuple Unpacking** (`a, b = b, a`, `first, *rest = items`) | 5 | 3 | Parser, Codegen |
| 67 | **Chained Comparisons** (`0 < x < 10`) | 4 | 2 | Parser, Desugar |
| 68 | **Context Managers** (`with resource as r:` for RAII) | 5 | 3 | Parser, Codegen, Runtime |
| 69 | **Spread Operators** (`[*a, *b]`, `{**d1, **d2}`) | 4 | 2 | Parser, Codegen |
| 70 | **Decorators** (`@cached fn foo():` - function transformers) | 4 | 3 | Parser, Codegen |
| 71 | **Attributes** (`#[inline]`, `#[deprecated]` - metadata) | 4 | 2 | Parser, Compiler |
| 72 | **Result Type** (`Result[T, E]` for error handling) | 5 | 2 | Type System, Stdlib |
| 73 | **`?` Operator** (error propagation, early return) | 5 | 2 | Parser, Desugar |
| 74 | **Match Guards** (`case x if cond:` - conditional patterns) | 4 | 2 | Parser, Pattern Matching |
| 75 | **If Let / While Let** (pattern in conditionals) | 3 | 2 | Parser, Desugar |
| 76 | **Derive Macros** (`#[derive(Debug, Clone)]`) | 4 | 3 | Parser, Codegen |
| 77 | **Move Closures** (`move \x: expr` - capture by value) | 3 | 3 | Parser, Closure Capture |
| 78 | **Associated Types** (`type Item` in traits) | 3 | 3 | Parser, Type System |
| 79 | **Where Clauses** (complex generic constraints) | 3 | 2 | Parser, Type System |
| 80 | **Or Patterns** (`1 | 2 | 3:` in match) | 4 | 2 | Parser, Pattern Matching |
| 81 | **Range Patterns** (`0..10:` in match) | 4 | 2 | Parser, Pattern Matching |
| 82 | **Auto-Forwarding Properties** (`get_`/`set_`/`is_` methods auto-create backing fields) | 4 | 3 | Parser, Type System, Semantic Analysis |
| 83 | **Isolated Threads** (`spawn_isolated` with copy/const only, channel communication) | 5 | 4 | Runtime, Type System, Scheduler |
| 84 | **Channel Types** (`Channel[T]` for thread-safe communication) | 5 | 3 | Runtime, Type System |
| 85 | **Send/Copy Traits** (type constraints for thread safety) | 4 | 3 | Type System |
| 86 | **Thread Pool** (`ThreadPool` for efficient parallel execution) | 4 | 3 | Runtime |
| 87 | **Unit Types** (`unit length(base: f64): m = 1.0, km = 1000.0`) | 4 | 3 | Parser, Type System |
| 88 | **Literal Suffixes** (`100_km`, `5_hr`, `42_uid` notation) | 4 | 2 | Lexer, Parser |
| 89 | **Composite Units** (`unit velocity = length / time`) | 4 | 4 | Type System, Codegen |
| 90 | **Composite Type Inference** (auto-infer `length / time → velocity`) | 5 | 4 | Type System |
| 91 | **Standalone Units** (`unit UserId: i64 as uid`) | 3 | 2 | Parser, Type System |
| 92 | **Primitive API Warnings** (warn on public primitive fields/params/returns) | 4 | 2 | Semantic Analysis, Linter |
| 93 | **Hexadecimal Literals** (`0xFF`, `0x1A2B`) | 5 | 1 | Lexer |
| 94 | **Binary Literals** (`0b1010`, `0b1111_0000`) | 4 | 1 | Lexer |
| 95 | **Octal Literals** (`0o755`, `0o17`) | 3 | 1 | Lexer |
| 96 | **Type Suffixes** (`42i32`, `3.14f64`) | 3 | 2 | Lexer, Parser |
| 97 | **Constructor Polymorphism** (`Constructor[T]` type for factory patterns) | 4 | 3 | Parser, Type System, Codegen |
| 98 | **Strong Enums** (`#[strong]` disallows wildcard `_` in pattern matching) | 4 | 2 | Parser, Pattern Matching, Semantic Analysis |
| 99 | **Body Block Outlining** (Actor/Generator/Future `body_block` to `fn(ctx)`) | 4 | 4 | MIR Transform, Codegen, Runtime FFI |
| 100 | **Capture Buffer & VReg Remapping** (ctx layout for outlined bodies) | 4 | 5 | MIR Liveness, Closure Encoding, Codegen |
| 101 | **Generator State Machine Codegen** (stackless yield/next) | 4 | 5 | MIR Transform, Runtime State, Codegen |
| 102 | **Future Body Execution** (compiled future resolves/awaits) | 4 | 4 | Runtime, Codegen, MIR Outlining |
| 103 | **Codegen Parity Completion** (remove stubs, pass full tests) | 5 | 5 | MIR, Codegen, Runtime |

### Difficulty-5 Breakdowns

| Parent | Sub-feature | Difficulty | Scope |
|--------|-------------|------------|-------|
| 100 | Capture liveness analysis | 3 | MIR dataflow |
| 100 | Capture buffer encode/decode | 3 | Codegen, Runtime |
| 101 | Yield-point discovery + state layout | 4 | MIR Transform |
| 101 | State dispatcher codegen | 4 | Codegen |
| 103 | Outlined block registration | 3 | MIR, Codegen |
| 103 | Runtime ctx ABI wiring | 3 | Runtime |
| 103 | Compiled actor/gen/future tests | 4 | Tests, Codegen |

## Dependency Guidelines (by module)
- **common**: shared contracts (ABI, GC handles, effect flags). Depends on nothing else.
- **parser**: implements syntax from the language spec; no runtime/loader dependency.
- **compiler**: depends on parser+common+runtime; targets ABIs defined in `common`; uses runtime for RuntimeValue types.
- **loader/native_loader**: dynamic loading only; no parser/compiler/runtime deps.
- **lib (native stdlib)**: uses loaders; avoid compiler/runtime coupling.
- **runtime**: implements ABIs declared in `common` (GC, scheduler) plus RuntimeValue types for codegen. No parser/compiler awareness.
- **driver**: orchestrates compile/load/run/watch via public interfaces; no deep coupling to compiler/runtime internals.

When implementing features above:
- Touch parser for syntax, compiler for lowering/codegen, runtime only via `common` ABI if needed.
- Keep memory/pointer semantics behind `common` GC ABI; stdlib/system features stay in `lib` + loaders.

---

## Codegen Implementation Status

The compiler uses a **hybrid execution model** where compilable features are compiled to native code via Cranelift, while unsupported features fall back to the tree-walking interpreter.

### MIR Instruction Coverage

| Category | Instructions | Codegen Status |
|----------|-------------|----------------|
| **Core** | ConstInt, ConstFloat, ConstBool, Copy, BinOp, UnaryOp | ✅ Implemented |
| **Memory** | Load, Store, LocalAddr, GetElementPtr | ✅ Implemented |
| **Control** | Call, Jump, Branch, Return | ✅ Implemented |
| **Collections** | ArrayLit, TupleLit, DictLit, IndexGet, IndexSet, Slice | ⚡ Stub (runtime FFI ready) |
| **Strings** | ConstString, ConstSymbol, FStringFormat | ⚡ Stub (runtime FFI ready) |
| **Closures** | ClosureCreate, IndirectCall | ⚡ Stub |
| **Objects** | StructInit, FieldGet, FieldSet | ⚡ Stub |
| **Methods** | MethodCallStatic, MethodCallVirtual, BuiltinMethod | ⚡ Stub |
| **Patterns** | PatternTest, PatternBind, EnumDiscriminant, EnumPayload | ⚡ Stub |
| **Enums** | EnumUnit, EnumWith | ⚡ Stub |
| **Async** | FutureCreate, Await, ActorSpawn, ActorSend, ActorRecv | 🔄 Interpreter fallback |
| **Generators** | GeneratorCreate, Yield, GeneratorNext | 🔄 Interpreter fallback |
| **Errors** | TryUnwrap, OptionSome, OptionNone, ResultOk, ResultErr | ⚡ Stub |
| **Fallback** | InterpCall, InterpEval | ✅ FFI bridge ready |

**Legend**: ✅ Implemented | ⚡ Stub (trap code) | 🔄 Interpreter fallback

### Runtime FFI Functions

The runtime provides FFI functions for codegen to call:

| Category | Functions |
|----------|-----------|
| **Value creation** | `rt_value_int`, `rt_value_float`, `rt_value_bool`, `rt_value_nil` |
| **Value extraction** | `rt_value_as_int`, `rt_value_as_float`, `rt_value_as_bool` |
| **Type checking** | `rt_value_is_nil`, `rt_value_is_int`, `rt_value_is_heap`, `rt_value_truthy` |
| **Array ops** | `rt_array_new`, `rt_array_len`, `rt_array_get`, `rt_array_set`, `rt_array_push`, `rt_array_pop` |
| **Tuple ops** | `rt_tuple_new`, `rt_tuple_len`, `rt_tuple_get`, `rt_tuple_set` |
| **String ops** | `rt_string_new`, `rt_string_len`, `rt_string_data`, `rt_string_concat` |
| **Generic ops** | `rt_index_get`, `rt_index_set`, `rt_slice` |

---

## Summary: 3 Key Points

### 1. Core Language Foundation Requires Multiple Interacting Components

The most essential features (basic types, variables, functions, control flow, structs/classes, enums) all have **Importance: 5** and require coordination across **Lexer, Parser, Type System, and Code Generation**. These form the minimal viable language and must be implemented together as they depend on each other. Pattern matching (difficulty 4) is critical because it underpins safe enum usage and Rust-like expressiveness.

### 2. Memory & Ownership is the Most Architecturally Complex Area

The memory system spans multiple pointer types (GC, unique, shared, weak, handle) with difficulty ratings of **4-5**. This affects:
- **Runtime**: GC implementation, reference counting, handle pools
- **Type System**: Borrow checking, lifetime analysis
- **Code Generation**: Different allocation strategies, RAII semantics

This is the hardest subsystem to get right and has the broadest architectural impact. Getting the GC-managed default correct is essential (Importance: 5, Difficulty: 5).

### 3. Concurrency Model is High-Value but High-Complexity

Actors, async effects, and stackless coroutines (all difficulty **5**) represent Simple's unique value proposition but require:
- **Runtime scheduler** for lightweight process management
- **Effect system** for compile-time async verification
- **State machine transformation** for stackless actors
- **Message queue infrastructure** for inter-actor communication

This layer sits on top of the memory system and type system, making it one of the last major features to implement but essential for the language's identity as a safe concurrent language.

### 4. Error Handling & Pattern Extensions (Rust-inspired)

Features #72-81 adopt Rust's proven error handling and pattern matching patterns:
- **Result[T, E] + `?` operator**: Explicit, composable error handling without exceptions
- **Match guards and or patterns**: More expressive pattern matching
- **Derive macros**: Reduce boilerplate for common traits

These features have **Importance: 3-5** and **Difficulty: 2-3**, making them high-value, moderate-effort additions that improve code safety and expressiveness.

### 5. Auto-Forwarding Properties (Encapsulation)

Feature #82 provides automatic property forwarding for cleaner encapsulation:
- Methods prefixed with `get_`, `set_`, or `is_` auto-create private `_` backing fields
- Type inference from accessor signatures
- Compile-time checks: duplicate field names, type mismatches, `is_` must return bool
- Read-only (`get_` only) or write-only (`set_` only) properties
- Internal methods access `_field` directly

This reduces boilerplate while maintaining explicit control over field access patterns.

### 6. Isolated Threads (Safe Parallelism)

Features #83-86 provide safe parallel execution without shared mutable state:
- **Isolated Threads**: `spawn_isolated` creates threads that can only access const globals and copied values
- **Channel Communication**: All inter-thread data transfer via typed `Channel[T]`
- **Send/Copy Traits**: Compile-time verification that types are safe to transfer
- **Thread Pool**: Efficient reuse of OS threads for parallel workloads

This model combines the safety of actors (no shared state) with the performance of real OS threads for CPU-bound parallelism.

### 7. Unit Types and Composite Type Inference

Features #87-91 provide type-safe dimensional values:
- **Unit Families**: `unit length(base: f64): m = 1.0, km = 1000.0` with auto-conversion
- **Literal Suffixes**: `100_km`, `5_hr` create typed values directly
- **Composite Units**: `unit velocity = length / time` defines derived units
- **Composite Type Inference**: `let speed = distance / time` auto-infers `velocity` type
- **Standalone Units**: `unit UserId: i64 as uid` for semantic wrapper types

This enables compile-time dimensional analysis preventing bugs like adding meters to seconds.

### 8. Type Safety and Numeric Literals

Features #92-96 improve type safety and numeric expressiveness:
- **Primitive API Warnings**: Encourages user-defined types over raw `i64`, `f64` in public APIs
- **Numeric Prefixes**: `0x` (hex), `0b` (binary), `0o` (octal) for different bases
- **Type Suffixes**: `42i32`, `3.14f64` for explicit literal types
- **Combined**: `0xFF_rgb`, `0b1010_flags` - prefix + unit suffix

This encourages semantic typing (`UserId` vs `i64`) and supports low-level bit manipulation.

### 9. Constructor Polymorphism and Strong Enums

Features #97-98 provide advanced type safety and factory patterns:
- **Constructor Polymorphism**: `Constructor[T]` type allows passing constructors as parameters for factory patterns. Child class constructors must be compatible with parent (same required params, extra params need defaults).
- **Strong Enums**: `#[strong]` attribute on enums disallows wildcard `_` patterns in match expressions, forcing exhaustive handling of all variants. Use `#[allow(wildcard)]` on specific match cases to opt-out.

These features improve type safety by ensuring factory patterns work correctly with inheritance and preventing accidental catch-all patterns that miss new enum variants.
