# Domain Research: Compiler/Interpreter Optimization + Syntax Sugar

**Date:** 2026-04-29
**Scope:** External lessons from Rust, Python, and JavaScript engines/languages that translate into concrete feature requests for Simple.

## Summary

The strongest cross-language pattern is:

1. **Do not jump straight from generic interpreter to heavy optimizer.**
2. **Use profiling feedback, specialization, and caching first.**
3. **Add syntax sugar that simplifies both user code and compiler internals, not just surface aesthetics.**

## Rust

### High-signal optimization lessons

- Official `rustc` guidance continues to emphasize **PGO**, **LTO/ThinLTO**, and codegen configuration as major performance levers.
- Cargo’s **incremental build cache** and **build timing reports** remain core workflow optimizations for large codebases.
- Recent stable Rust changes also show value in **toolchain ergonomics** and explicit performance controls, not only language semantics.

### High-signal syntax/ergonomic lessons

- Rust 2024 and recent stable releases add targeted sugar that improves compiler-facing code quality:
  - `let` chains in `if` / `while`
  - `if let` guards in `match`
  - `async` closures
  - more precise `impl Trait` capture control

### Translation to Simple

Rust suggests Simple should prioritize:

- compile timing visibility,
- cached artifacts for repeated work,
- whole-program optimization modes for native output,
- and compact conditional/pattern sugar for compiler passes and interpreters.

### Rust sources

- https://doc.rust-lang.org/rustc/profile-guided-optimization.html
- https://doc.rust-lang.org/rustc/codegen-options/
- https://doc.rust-lang.org/cargo/reference/build-cache.html
- https://doc.rust-lang.org/cargo/reference/timings.html
- https://doc.rust-lang.org/edition-guide/rust-2024/let-chains.html
- https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/
- https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/

## Python

### High-signal optimization lessons

- CPython’s **specializing adaptive interpreter** (`PEP 659`) is the clearest proof that interpreter specialization can deliver large wins before a mature JIT exists.
- Python 3.12’s **comprehension inlining** (`PEP 709`) shows that desugared helper constructs should not automatically become helper frames/functions at runtime.
- Python’s newer tiering work and experimental JIT (`PEP 744`) show the value of:
  - shared instruction definitions,
  - a staged optimizer path,
  - and reuse of profiling data across tiers.

### High-signal syntax/ergonomic lessons

- `PEP 695`: compact type-parameter syntax and type aliases.
- `PEP 701`: parser-visible interpolation grammar instead of ad hoc string parsing.
- `PEP 750`: structured template strings for safe deferred rendering.

### Translation to Simple

Python suggests Simple should prioritize:

- adaptive opcode specialization,
- inline caches,
- helper-frame elision for lowered sugar,
- a shared instruction DSL or metadata source,
- and structured interpolation/template forms.

### Python sources

- https://peps.python.org/pep-0659/
- https://peps.python.org/pep-0709/
- https://peps.python.org/pep-0744/
- https://peps.python.org/pep-0695/
- https://peps.python.org/pep-0701/
- https://peps.python.org/pep-0750/
- https://docs.python.org/3.14/library/concurrent.interpreters.html
- https://docs.python.org/3/howto/free-threading-python.html

## JavaScript

### High-signal optimization lessons

- Modern JS engines converge on **tiered execution** with shared profiling feedback.
- They rely heavily on **inline caches** and **specialized fast paths**.
- They invest directly in **startup latency**, **bytecode/code caching**, and lower-memory execution paths.
- Recent V8 work also shows a push toward **CFG/SSA middle-end structure** for maintainability and deopt support.

### High-signal syntax/ergonomic lessons

- Iterator helpers provide lazy collection ergonomics without mandatory eager allocation.
- Explicit resource management (`using`, `await using`, `DisposableStack`) shows how small syntax/library additions can raise code safety.
- Import attributes show a cleaner path for typed or host-aware loading than magic imports.

### Translation to Simple

JavaScript suggests Simple should prioritize:

- shared profile/IC infrastructure,
- a mid-tier optimizer for hot code,
- cross-session bytecode/module caching,
- iterator-helper ergonomics desugared to loops,
- and import metadata syntax.

### JavaScript sources

- https://v8.dev/blog/maglev
- https://v8.dev/blog/leaving-the-sea-of-nodes
- https://v8.dev/blog/explicit-compile-hints
- https://v8.dev/blog/improved-code-caching
- https://v8.dev/blog/mutable-heap-number
- https://hacks.mozilla.org/2020/11/warp-improved-js-performance-in-firefox-83/
- https://webkit.org/blog/10308/speculation-in-javascriptcore/
- https://webkit.org/blog/15249/optimizing-webkit-safari-for-speedometer-3-0/
- https://github.com/tc39/proposal-iterator-helpers
- https://github.com/tc39/proposal-set-methods
- https://github.com/tc39/proposal-explicit-resource-management
- https://github.com/tc39/proposal-import-attributes

## Cross-Language Synthesis

The most defensible feature-request themes for Simple are:

### Optimization

1. **Adaptive specialization before full JIT**
2. **Inline caches as a reusable primitive**
3. **Mid-tier IR between interpreter and heavyweight native optimization**
4. **Compile/startup visibility and cross-session caching**
5. **Whole-program native optimization only after measurement justifies it**

### Syntax sugar

1. **Control-flow sugar that simplifies compiler code**
2. **Structured interpolation/template forms**
3. **Predictable lazy-iterator ergonomics**
4. **Typed import metadata**

## Recommended Feature Requests

### Performance-focused

- Adaptive opcode specialization with inline caches.
- Cross-session bytecode/module cache.
- Compile timing and stage profiling report.
- Mid-tier micro-op or CFG/SSA optimizer path.
- Runtime feature gating for optional subsystems.

### Syntax-focused

- Let chains in `if` / `while`.
- `match` guards with pattern bindings.
- Structured template strings.
- Import attributes.
- Lazy iterator helpers desugared to loops.

## Notes

- Some older sugar categories are already present in Simple, so not every Rust/Python/JS feature maps to a worthwhile request.
- The best next step is not implementation; it is choosing a requirement option that fixes the scope and the non-functional targets.
