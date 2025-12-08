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
| 32 | **Waitless Effects** | 3 | 5 | Type System, Effect Analysis, Runtime Guards |
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

## Dependency Guidelines (by module)
- **common**: shared contracts (ABI, GC handles, effect flags). Depends on nothing else.
- **parser**: implements syntax from the language spec; no runtime/loader dependency.
- **compiler**: depends on parser+common; targets ABIs defined in `common`; avoid runtime/internal deps.
- **loader/native_loader**: dynamic loading only; no parser/compiler/runtime deps.
- **lib (native stdlib)**: uses loaders; avoid compiler/runtime coupling.
- **runtime**: implements ABIs declared in `common` (GC, scheduler). No parser/compiler awareness.
- **driver**: orchestrates compile/load/run/watch via public interfaces; no deep coupling to compiler/runtime internals.

When implementing features above:
- Touch parser for syntax, compiler for lowering/codegen, runtime only via `common` ABI if needed.
- Keep memory/pointer semantics behind `common` GC ABI; stdlib/system features stay in `lib` + loaders.

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

Actors, waitless effects, and stackless coroutines (all difficulty **5**) represent Simple's unique value proposition but require:
- **Runtime scheduler** for lightweight process management
- **Effect system** for compile-time waitless verification
- **State machine transformation** for stackless actors
- **Message queue infrastructure** for inter-actor communication

This layer sits on top of the memory system and type system, making it one of the last major features to implement but essential for the language's identity as a safe concurrent language.
