# Simple Language - Not Yet Implemented Features

**Last Updated:** 2025-12-14  
**Source:** Compiled from `doc/feature.md` and `doc/status/` directory

This document tracks all features from `feature.md` that are **not yet fully implemented**. Features are organized by priority and implementation complexity.

---

## Critical Path Features (Importance: 5, Not Complete)

### 1. Type Inference (#13) - PARTIAL ⚡
- **Status:** HM scaffold working, needs full integration
- **Difficulty:** 4/5
- **What's Done:**
  - ✅ Unification algorithm with occurs check
  - ✅ Substitution tracking
  - ✅ Basic expression inference (literals, binops, arrays, if, index, calls)
  - ✅ Function/struct/class/enum registration
- **What's Missing:**
  - ❌ Generalization at let-binding (polymorphic lets)
  - ❌ Instantiation at use sites
  - ❌ Integration with HIR for native codegen
  - ❌ Better error messages with source spans
- **Files:** `src/type/src/lib.rs`, `src/compiler/src/pipeline.rs`
- **Tests:** 22 passing in `simple-type`

### 2. Codegen Parity Completion (#103) - PARTIAL ⚡
- **Status:** Hybrid execution (compiled + interpreter fallback)
- **Difficulty:** 5/5
- **What's Done:**
  - ✅ Core instructions (ConstInt/Float/Bool, Copy, BinOp, UnaryOp)
  - ✅ Memory (Load, Store, LocalAddr, GetElementPtr)
  - ✅ Control flow (Call, Jump, Branch, Return)
  - ✅ Outlined body plumbing for actors/futures/generators
  - ✅ Cranelift backend (default)
  - ✅ LLVM backend (32-bit + 64-bit, 43 tests passing)
  - ✅ Runtime FFI (50+ functions for collections, strings, etc.)
- **What's Missing:**
  - ❌ Collections codegen (ArrayLit, TupleLit, DictLit, IndexGet/Set, Slice) - **stubs only**
  - ❌ String codegen (ConstString, ConstSymbol, FStringFormat) - **stubs only**
  - ❌ Closures (ClosureCreate, IndirectCall) - **stubs only**
  - ❌ Objects (StructInit, FieldGet, FieldSet) - **stubs only**
  - ❌ Methods (MethodCallStatic/Virtual, BuiltinMethod) - **stubs only**
  - ❌ Patterns (PatternTest, PatternBind, EnumDiscriminant/Payload) - **stubs only**
  - ❌ Enums (EnumUnit, EnumWith) - **stubs only**
  - ❌ Errors (TryUnwrap, Option*, Result*) - **stubs only**
  - ❌ Generator state machine codegen (#101) - **interpreter fallback**
  - ❌ Future body execution (#102) - **interpreter fallback**
  - ❌ Compiled integration tests for actors/futures/generators
- **Files:** `src/compiler/src/codegen/`, `src/runtime/src/value/`
- **See:** `doc/status/codegen_parity_completion.md`

### 3. Symbol Resolution (#116) - IN PROGRESS 🔄
- **Status:** Module resolution complete, cross-module symbol lookup pending
- **Difficulty:** 4/5
- **What's Done:**
  - ✅ FileSystem abstraction
  - ✅ ModPath/Segment types with validation
  - ✅ Module resolution (toFilePath/toDirPath, resolve())
  - ✅ Visibility export (effectiveVisibility, ancestorVisibility)
  - ✅ Macro auto-import (isAutoImported, globImport filtering)
  - ✅ SymbolTable per module
  - ✅ Import graph construction
  - ✅ Circular dependency detection
- **What's Missing:**
  - ❌ Cross-module symbol lookup implementation
  - ❌ Integration with compiler pipeline
  - ❌ Multi-file compilation support
- **Files:** `src/compiler/src/module_resolver.rs`, `src/compiler/src/project.rs`

---

## High-Value Features (Importance: 4-5, Not Started)

### 4. Unique Pointers (&T, RAII) (#25)
- **Status:** NOT STARTED
- **Difficulty:** 4/5
- **Requires:** Type system, borrow checking, codegen
- **Impact:** Memory safety without GC overhead

### 5. Shared Pointers (*T, refcounting) (#26)
- **Status:** NOT STARTED
- **Difficulty:** 4/5
- **Requires:** Runtime, type system, codegen
- **Impact:** Shared ownership semantics

### 6. Weak Pointers (-T) (#27)
- **Status:** NOT STARTED
- **Difficulty:** 3/5
- **Requires:** Shared pointers implementation
- **Impact:** Break reference cycles

### 7. Handle Pointers (+T, handle pools) (#28)
- **Status:** NOT STARTED
- **Difficulty:** 4/5
- **Requires:** Runtime, type system, pool management
- **Impact:** Efficient resource handles (file descriptors, sockets)

### 8. Traits (#15)
- **Status:** NOT STARTED
- **Difficulty:** 4/5
- **Requires:** Parser, type system, vtables/codegen
- **Impact:** Polymorphism and interfaces

### 9. Impl Blocks (#16)
- **Status:** NOT STARTED
- **Difficulty:** 3/5
- **Requires:** Parser, type system, method resolution
- **Impact:** Method organization

### 10. Lambdas/Closures (\x: expr) (#17)
- **Status:** NOT STARTED
- **Difficulty:** 4/5
- **Requires:** Parser, type system, closure capture, codegen
- **Impact:** Functional programming support

### 11. Union Types (A | B) (#37)
- **Status:** NOT STARTED
- **Difficulty:** 4/5
- **Requires:** Type system, codegen
- **Impact:** Type flexibility

---

## Testing & Tooling (High Priority)

### 12. BDD Spec Framework (#300) - 70% COMPLETE 🔄
- **Difficulty:** 4/5
- **Sprint 1:** ✅ Complete (9/12 tasks: DSL, Registry, Runtime, Matchers)
- **Sprint 2:** ❌ Runner CLI, Executor, Formatters
- **Sprint 3:** ❌ Coverage tracker and reporter
- **See:** `doc/feature.md` lines 293-315, `doc/plans/28_bdd_spec.md`

### 13. Simple Doctest (sdoctest) (#301) - 90% EFFECTIVE COMPLETE 🔄
- **Difficulty:** 4/5
- **Sprint 1-2:** ✅ Complete (15/16 non-blocked tasks: Parser, Matcher, Runner, Discovery, FFI)
- **Blocked:** CLI integration, Simple runtime execution, BDD integration
- **Sprint 3-4:** ❌ Tag filtering, REPL recording, Coverage
- **See:** `doc/feature.md` lines 317-345, `doc/plans/29_doctest.md`

### 14. Test CLI Integration (#302) - NOT STARTED 📋
- **Difficulty:** 3/5
- **Missing:** CLI command, test filtering, discovery, unified reporting, coverage reports
- **Requires:** BDD framework, Doctest framework
- **See:** `doc/feature.md` lines 356-366

### 15. JJ Version Control Integration (#303) - 67% COMPLETE 🔄
- **Difficulty:** 3/5 (varies)
- **Done:** 8/12 tasks (state manager, connector, CLI --snapshot flag, 17 tests)
- **Missing:** Test success tracking (blocked), system tests, documentation
- **Usage:** `simple compile app.spl --snapshot`
- **See:** `doc/feature.md` lines 368-386, `doc/plans/27_jj_integration.md`

---

## Standard Library Features (Not Implemented)

### 16. Comprehensions
- **List Comprehension** (#62): `[x*2 for x in items]` - NOT STARTED
- **Dict Comprehension** (#63): `{k: v for k,v in pairs}` - NOT STARTED
- **Difficulty:** 3/5 each
- **Requires:** Parser, codegen

### 17. Advanced Patterns
- **Slicing** (#64): `items[1:3]`, `items[::2]`, `items[::-1]` - NOT STARTED
- **Negative Indexing** (#65): `items[-1]` - NOT STARTED
- **Tuple Unpacking** (#66): `a, b = b, a`, `first, *rest = items` - NOT STARTED
- **Difficulty:** 2-3/5
- **Requires:** Parser, runtime

### 18. Context Managers
- **Context Managers** (#68): `with resource as r:` for RAII - NOT STARTED
- **Difficulty:** 3/5
- **Requires:** Parser, codegen, runtime

### 19. Error Handling Ergonomics
- **`?` Operator** (#73): Error propagation, early return - NOT STARTED
- **Match Guards** (#74): `case x if cond:` - NOT STARTED
- **If Let / While Let** (#75): Pattern in conditionals - NOT STARTED
- **Difficulty:** 2/5 each
- **Requires:** Parser, desugar

### 20. Concurrency
- **Isolated Threads** (#83): `spawn_isolated` with copy/const only - NOT STARTED
- **Channel Types** (#84): `Channel[T]` for thread-safe communication - NOT STARTED
- **Send/Copy Traits** (#85): Type constraints for thread safety - NOT STARTED
- **Thread Pool** (#86): Efficient parallel execution - NOT STARTED
- **Difficulty:** 3-4/5
- **Requires:** Runtime, type system, scheduler

---

## Unit Types & Semantic Typing (Not Implemented)

### 21. Unit System (#87-91)
- **Unit Types** (#87): `unit length(base: f64): m = 1.0, km = 1000.0` - NOT STARTED
- **Literal Suffixes** (#88): `100_km`, `5_hr` notation - NOT STARTED
- **Composite Units** (#89): `unit velocity = length / time` - NOT STARTED
- **Composite Type Inference** (#90): Auto-infer `length / time → velocity` - NOT STARTED
- **Standalone Units** (#91): `unit UserId: i64 as uid` - NOT STARTED
- **Difficulty:** 2-4/5
- **Requires:** Parser, type system, codegen

### 22. String Units (#200-209)
- **Bare String Lint** (#200): Warn on public APIs using `str` - NOT STARTED
- **String Unit Suffixes** (#201): `"path"_file`, `"ip"_ip` - NOT STARTED
- **FilePath** (#202), **IpAddr** (#204), **Port** (#205), **SocketAddr** (#206) - NOT STARTED
- **Url Types** (#207-209): Generic, HTTP, FTP URLs - NOT STARTED
- **Difficulty:** 1-3/5
- **Requires:** Parser, type system, stdlib

### 23. Network & HTTP (#210-215)
- **TCP/UDP Async API** (#210-211) - NOT STARTED
- **HTTP Client** (#212) - NOT STARTED
- **FTP Client** (#213) - NOT STARTED
- **StatusCode/Header Units** (#214-215) - NOT STARTED
- **Difficulty:** 3-4/5
- **Requires:** Runtime, stdlib, async

### 24. ByteCount Unit Family (#216)
- **Status:** NOT STARTED
- **Units:** bytes, kb, mb, gb, tb
- **Difficulty:** 2/5

---

## GPU & SIMD Features (Not Implemented)

### 25. SIMD (#118-123)
- **SIMD Vector Types** (#118): `vec[N, T]` - NOT STARTED
- **SIMD Arithmetic** (#119): Lane-wise ops - NOT STARTED
- **SIMD Reductions** (#120): sum, product, min, max - NOT STARTED
- **SIMD Shuffles** (#121): swizzle, blend, gather, scatter - NOT STARTED
- **SIMD Load/Store** (#122): aligned/masked - NOT STARTED
- **SIMD Math** (#123): sqrt, abs, fma, floor, ceil - NOT STARTED
- **Difficulty:** 3-4/5
- **Requires:** Parser, type system, codegen, runtime

### 26. GPU Support (#124-129)
- **GPU Context** (#124): device discovery, context creation - NOT STARTED
- **GPU Buffers** (#125): alloc, upload, download, map - NOT STARTED
- **GPU Kernels** (#126): `#[gpu]` attribute for compute kernels - PLANNED 📋
- **GPU Launch** (#127): kernel dispatch, work groups, sync - NOT STARTED
- **GPU Intrinsics** (#128): global_id, local_id, barrier, atomics - NOT STARTED
- **GPU Shared Memory** (#129): `shared let` for work group storage - NOT STARTED
- **Difficulty:** 4-5/5
- **Requires:** Parser, compiler, SPIR-V codegen, runtime
- **See:** `doc/plans/26_gpu_kernels.md` (for #126)

---

## Advanced Language Features (Not Implemented)

### 27. Metaprogramming
- **Derive Macros** (#76): `#[derive(Debug, Clone)]` - NOT STARTED
- **Context Blocks** (#35): DSL support - NOT STARTED
- **Method Missing** (#36): Dynamic dispatch - NOT STARTED
- **Difficulty:** 3-4/5

### 28. Miscellaneous
- **Named Arguments** (#18) - NOT STARTED
- **Trailing Blocks** (#19) - NOT STARTED
- **Functional Update** (#20): `->` operator - NOT STARTED
- **Symbols/Atoms** (#39): `:symbol` - NOT STARTED
- **No-Parentheses Calls** (#47) - NOT STARTED
- **Difficulty:** 2-3/5

### 29. Advanced Types
- **Associated Types** (#78): `type Item` in traits - NOT STARTED
- **Where Clauses** (#79): Complex generic constraints - NOT STARTED
- **Or Patterns** (#80): `1 | 2 | 3:` in match - NOT STARTED
- **Range Patterns** (#81): `0..10:` in match - NOT STARTED
- **Difficulty:** 2-3/5

### 30. Constructor & Enums
- **Constructor Polymorphism** (#97): `Constructor[T]` type - NOT STARTED
- **Strong Enums** (#98): `#[strong]` disallows wildcard `_` - NOT STARTED
- **Difficulty:** 2-3/5

### 31. Multi-Base Unit Types (#219)
- **Status:** NOT STARTED
- **Feature:** `unit IpAddr: str | u32 as ip` - multiple literal forms
- **Difficulty:** 3/5

---

## UI/Web Framework (Planned)

### 32. UI Framework (#500-514) - PLANNED 📋
**Total:** 15 features  
**Difficulty:** 3-5/5 (varies)  
**Status:** Complete specification, not started

**Key Features:**
- Unified `.sui` syntax with `{@ $}` `{- +}` `{{ }}` `{% %}` blocks
- Dual renderer (GUI + TUI from same source)
- Shared state model, server/client execution
- Dynamic structure (if/for), SSR + hydration

**See:** `doc/ui.md` (spec), `doc/feature.md` lines 500-514 (breakdown), `doc/status/ui_*.md`

### 33. Web Framework (#520-536) - PLANNED 📋
**Total:** 17 features  
**Difficulty:** 2-5/5 (varies)  
**Status:** Complete specification, not started

**Key Features:**
- Rails-like routing and controllers
- Spring-inspired DI and auto-config
- Convention-based rendering (controller → .sui)
- Production endpoints (/health, /metrics)
- Enforced layering (controller → service → infra)

**See:** `doc/web_framework.md` (spec), `doc/feature.md` lines 520-536 (breakdown)

---

## LLM-Friendly Features (#400-410) - PLANNED 📋

**Total:** 11 features, ~98 hours estimated  
**Priority:** High (makes Simple optimal for AI-assisted development)

| Feature | Difficulty | Priority | Status |
|---------|------------|----------|--------|
| Contract Blocks (#400) | 4/5 | ⭐⭐⭐ Highest | Planned |
| Capability-Based Imports (#401) | 4/5 | ⭐⭐⭐ Critical | Planned |
| Extended Effect System (#402) | 3/5 | ⭐⭐⭐ | Planned |
| AST/IR Export (#403) | 3/5 | ⭐⭐ | Planned |
| Structured Diagnostics (#404) | 2/5 | ⭐⭐ | Planned |
| Context Pack Generator (#405) | 3/5 | ⭐⭐ | Planned |
| Property-Based Testing (#406) | 4/5 | ⭐ | Planned |
| Snapshot/Golden Tests (#407) | 3/5 | ⭐ | Planned |
| Provenance Annotations (#408) | 2/5 | ⭐ | Planned |
| Forbidden Pattern Linter (#409) | 3/5 | ⭐ | Planned |
| Semantic Diff Tool (#410) | 3/5 | ⭐ | Planned |

**See:** `doc/feature.md` lines 400-410 (detailed descriptions), `doc/plans/llm_friendly.md` (implementation plan)

---

## Future/Low Priority Features

### 45. Developer Tooling (Pending)
- **Language Server Protocol (LSP)** - Medium priority, 40h
- **Debugger (DAP)** - Medium priority, 50h
- **Convention Over Configuration** - Medium priority, 15h
- **See:** `doc/plans/30_pending_features.md`

### 46. GUI/UI Support (Low Priority)
- **TUI Framework** - Medium priority, 30h
- **GUI Framework** - Low priority, 150h+
- **See:** `doc/plans/30_pending_features.md`

### 47. Infrastructure (TBD)
- **Package Registry** - Medium priority, 60h
- **Build System Enhancements** - TBD
- **See:** `doc/plans/30_pending_features.md`

---

## Summary Statistics

**Total Features in feature.md:** 536+  
**Fully Complete:** ~100 (19%)  
**Partial/In Progress:** ~15 (3%)  
**Not Started:** ~421 (78%)

**By Importance:**
- Importance 5: ~50 features (30% complete)
- Importance 4: ~80 features (20% complete)
- Importance 3: ~120 features (15% complete)
- Importance 2: ~60 features (5% complete)

**By Difficulty:**
- Difficulty 5: ~25 features (40% complete - runtime/codegen done)
- Difficulty 4: ~80 features (25% complete)
- Difficulty 3: ~150 features (15% complete)
- Difficulty 2: ~180 features (10% complete)
- Difficulty 1: ~100 features (50% complete - basics done)

**Critical Path (Importance 5, Not Complete):**
1. Type Inference (#13) - PARTIAL
2. Codegen Parity (#103) - PARTIAL
3. Symbol Resolution (#116) - IN PROGRESS

**High-Value Next Steps:**
1. Complete codegen stubs (collections, strings, structs, enums, methods)
2. Finish type inference (generalization, instantiation)
3. Implement cross-module symbol lookup
4. Complete BDD/Doctest CLI integration
5. Implement unique/shared/weak/handle pointers
6. Add traits and impl blocks

---

## See Also

- `CLAUDE.md` - Current implementation status
- `doc/feature.md` - Complete feature list with ratings
- `doc/status/` - Per-feature status files (79+ files)
- `doc/plans/` - Implementation plans
- `doc/plans/30_pending_features.md` - Future development priorities
