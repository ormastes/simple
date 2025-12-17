# Simple Language Features

**Last Updated:** 2025-12-17

## Summary Statistics

**Overall Progress:** 68% (90/133 features complete, 10 in progress)

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 47 | 45 | 1 | 1 |
| Codegen | 5 | 4 | 1 | 0 |
| Testing & CLI | 4 | 4 | 0 | 0 |
| Concurrency Runtime | 4 | 4 | 0 | 0 |
| Contracts | 6 | 6 | 0 | 0 |
| Extended - Units | 16 | 10 | 0 | 6 |
| Extended - Networking | 6 | 6 | 0 | 0 |
| Advanced - Effects | 6 | 6 | 0 | 0 |
| Advanced - UI | 3 | 0 | 0 | 3 |
| Advanced - Web | 17 | 0 | 0 | 17 |
| Advanced - GPU/SIMD | 19 | 5 | 8 | 6 |

**Test Status:** 1058+ tests passing (24 stdlib, 700+ driver, 332 compiler)

---

## Recent Work (Dec 2025)

### Contract Test Fix (2025-12-17)
| Feature | Status | Description |
|---------|--------|-------------|
| Contract tests | ✅ | Fixed 12 tests with wrong syntax (contracts go INSIDE body, not before colon) |
| All contracts | ✅ | Parser, MIR lowering, codegen all working (332 compiler tests pass) |

### Interpreter Enhancements (2025-12-17)
| Feature | Status | Description |
|---------|--------|-------------|
| String methods | ✅ | `find_str`, `trimmed`, `sorted`, `taken`, `dropped`, `appended`, `prepended`, `push`, `push_str`, `pop`, `clear` |
| Option methods | ✅ | `or`, `ok_or` |
| Result methods | ✅ | `or` |
| BDD skip | ✅ | `skip` builtin for skipped tests |

### Previous Completions
| Feature | Status | Description |
|---------|--------|-------------|
| **Type Inference (HM)** | ✅ | Unification, constraint solving, 68 unit + 32 integration tests |
| **Associated Types** | ✅ | Trait-associated type members (5 parser tests) |
| **Dynamic Dispatch (dyn Trait)** | ✅ | TraitObject coercion in let/parameters (4 tests) |
| **Memory Pointers (#25-28)** | ✅ | Unique, Shared, Weak, Handle pointers (17 tests) |
| **Context Blocks (#35)** | ✅ | DSL context dispatch (3 tests) |
| **Method Missing (#36)** | ✅ | Dynamic method fallback (3 tests) |
| **Effects (EFF-001-006)** | ✅ | Algebraic effects, handlers, inference (39 tests) |
| Pattern Matching | ✅ | All pattern types (79 BDD tests) |
| Where Clauses | ✅ | Generic trait bounds (`where T: Clone + Default`) |
| Concurrency Primitives | ✅ | Mutex, RwLock, Semaphore, Barrier |

---

## In Progress Features

### Core Language

| Feature | Status | Blocker |
|---------|--------|---------|
| Type Inference (#13) | 🔄 | Full AST integration needed |
| Union Types (#37) | 📋 | Design required |

### Codegen

| Feature | Status | Notes |
|---------|--------|-------|
| Future Body (#102) | 🔄 | Eager execution done, async state machine pending |
| Codegen Parity (#103) | 🔄 | InterpCall/InterpEval defined but not emitted |

### GPU & SIMD (#400-418)

| Feature | Status | Notes |
|---------|--------|-------|
| SIMD vectors (#400) | 🔄 | MIR support, codegen pending |
| Vector arithmetic (#401) | 🔄 | MIR support |
| GPU kernels (#405) | 🔄 | Basic support, attribute parsing pending |
| Thread blocks (#406) | 🔄 | MIR support complete |
| Shared memory (#407) | 🔄 | MIR GpuSharedAlloc complete |
| Synchronization (#408) | 🔄 | GpuBarrier, GpuMemFence complete |
| Atomic operations (#409) | 🔄 | GpuAtomic complete (9 ops) |
| GPU device API (#410) | 🔄 | CUDA runtime wrapper |

---

## Completed Features

### Memory & Pointers ✅

All pointer types implemented and tested (17 tests pass):
- Unique Pointers (`new &`) ✅
- Shared Pointers (`new *`) ✅
- Weak Pointers (`new -`) ✅
- Handle Pointers (`new +`) ✅
- Borrows (`&x`, `&mut x`) ✅

### Contracts (#400-405) ✅

Design by Contract fully implemented (12 tests pass):

| Feature | Status | Description |
|---------|--------|-------------|
| Preconditions (`in:`) | ✅ | Entry condition checks |
| Postconditions (`out:`) | ✅ | Success exit condition checks |
| Error postconditions (`out_err:`) | ✅ | Error exit condition checks |
| Invariants (`invariant:`) | ✅ | Class/method invariants |
| Old value capture (`old()`) | ✅ | Snapshot values at entry for postconditions |
| Result binding | ✅ | `out(ret):` binds return value |

**Syntax:** Contracts go INSIDE function body after the colon:
```simple
fn divide(a: i64, b: i64) -> i64:
    in:
        b != 0
    out(ret):
        ret * b == a
    return a / b
```

### Unit Types (#200-219) ✅

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #200 | Numeric units | ✅ | `_km`, `_hr`, `_bytes` suffixes (14 tests) |
| #201 | Unit families | ✅ | Family definitions with conversion factors |
| #202 | String units | ✅ | `"127.0.0.1"_ip`, `"foo"_regex` suffixes |
| #203 | Type-safe arithmetic | ✅ | `allow add/sub/mul/div/neg` rules |
| #204 | Unit conversion | ✅ | `.to_X()` methods with factor conversion |
| #205 | Custom units | ✅ | `unit UserId: u64 as uid` parsing |
| #206 | Compound units | ✅ | `unit velocity = length / time` |
| #207 | SI prefixes | ✅ | kilo, mega, giga auto-detection (10 tests) |
| #208 | Unit inference | ✅ | Parameter/return type validation |
| #209 | Unit assertions | ✅ | assert_unit! macro + let binding validation |
| #210 | Bit-limited repr | 📋 | `repr:` block in unit families for allowed representations |
| #211 | Compact repr syntax | 📋 | `_cm:u12` colon notation for bit-width specification |
| #212 | Range inference | 📋 | `where range: 0..1000` auto-infers u10 |
| #213 | Overflow behaviors | 📋 | `checked`, `saturate`, `wrap` constraints |
| #214 | Unit widening | 📋 | `.widen()`, `.narrow()`, `.saturate()` conversions |
| #215 | Bitfield units | 📋 | Unit types in bitfield fields with type safety |

### Networking (#220-225) ✅

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #220 | TCP sockets | ✅ | bind, accept, connect, read, write, close |
| #221 | UDP sockets | ✅ | bind, recv, send, recv_from, send_to |
| #222 | HTTP client | ✅ | Basic client support |
| #223-225 | Advanced | ✅ | Socket options, timeouts |

---

## Planned Features

### UI Framework (#510-512) 📋

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #510 | .sui file format | 📋 | Structural UI definition files |
| #511 | Structural PatchSet | 📋 | Reactive updates |
| #512 | SSR + Hydration | 📋 | Server-side rendering |

### Web Framework (#520-536) 📋

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #520 | Routing | 📋 | URL to handler mapping |
| #521 | Controllers | 📋 | Request handlers |
| #522 | Middleware | 📋 | Request/response pipeline |
| #523 | Templates | 📋 | HTML generation |
| #524-528 | Core features | 📋 | Sessions, auth, REST API |
| #529-536 | Advanced | 📋 | GraphQL, WebSocket, ORM, caching |

### GPU Safety Features (#411-418) 📋

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #411 | Bounds policy | 📋 | `@bounds(default=return)` |
| #412 | bounds: clause | 📋 | Pattern-based bounds handlers |
| #413 | Indexer trait | 📋 | User-defined indexing |
| #414 | Neighbor accessors | 📋 | `.left_neighbor`, `.right_neighbor` |
| #415 | Parallel iterators | 📋 | `par_map`, `par_reduce` |
| #416 | Tensor operations | 📋 | Multi-dimensional arrays |

---

## Known Issues

| Issue | Description | Priority |
|-------|-------------|----------|
| Collection mutation | Array/List/Dict changes don't persist | High |
| Type annotation scope | Variables inaccessible after `let x: T = v` | Medium |
| Doctest framework | Requires List mutation and Set | Low |

---

## Next Priorities

### Immediate (Sprint)
1. **Collection mutation** - Fix Array/List/Dict persistence
2. **Type annotation scope** - Fix variable accessibility bug

### Short Term (Month)
1. Union types (#37) - Tagged union syntax
2. Result type (#37b) - `Result[T, E]` with `?` operator
3. Full type inference (#13) - AST integration

### Medium Term (Quarter)
1. GPU kernel features (#405-410) - MIR-to-codegen path
2. SIMD operations (#400-404) - CPU vector support
3. UI framework prototype (#510-512)
4. Web framework basics (#520-536)

---

## Status Legend

- ✅ **COMPLETE** - Fully implemented and tested
- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet implemented
- 🔮 **FUTURE** - Long-term goal

## Related Documentation

- `FEATURE_STATUS.md`: Comprehensive status tracking
- `status/*.md`: Individual feature documentation (63+ files)
- `codegen_status.md`: MIR instruction coverage, runtime FFI
- `architecture.md`: Design principles and dependency rules
- `CLAUDE.md`: Development guide for contributors
