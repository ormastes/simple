# Simple Language Features

## Summary Statistics

**Overall Progress:** 81% (170/211 features complete, 0 in progress)

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 47 | 47 | 0 | 0 |
| Codegen | 6 | 6 | 0 | 0 |
| Testing & CLI | 39 | 39 | 0 | 0 |
| Concurrency Runtime | 33 | 33 | 0 | 0 |
| Contracts | 32 | 32 | 0 | 0 |
| Extended - Units | 10 | 7 | 0 | 3 |
| Extended - Networking | 6 | 0 | 0 | 6 |
| Advanced - Effects | 6 | 6 | 0 | 0 |
| Advanced - UI | 6 | 0 | 0 | 6 |
| Advanced - Web | 17 | 0 | 0 | 17 |
| Advanced - GPU/SIMD | 11 | 0 | 0 | 11 |

**Completed features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md)

---

## Recent Completions (Dec 2025)

| Feature | Status | Description |
|---------|--------|-------------|
| **Type Inference (HM)** | ✅ | Unification, constraint solving, 68 unit + 32 integration tests |
| **Associated Types** | ✅ | Trait-associated type members (5 parser tests) |
| **Dynamic Dispatch (dyn Trait)** | ✅ | TraitObject coercion in let/parameters (4 tests) |
| **Numeric Units (#200)** | ✅ | `_km`, `_bytes` suffixes (5 tests) |
| **String Units (#202)** | ✅ | `"value"_ip` suffixes |
| **Custom Units (#205)** | ✅ | `unit UserId: u64 as uid` parsing |
| **Memory Pointers (#25-28)** | ✅ | Unique, Shared, Weak, Handle pointers (17 tests) |
| **Context Blocks (#35)** | ✅ | DSL context dispatch (3 tests) |
| **Method Missing (#36)** | ✅ | Dynamic method fallback (3 tests) |
| **Effects (EFF-001-006)** | ✅ | Algebraic effects, handlers, inference (39 tests) |
| **Contracts (CTR-001-062)** | ✅ | Full Design-by-Contract system |
| Codegen Parity (#99-103) | ✅ | Body outlining, hybrid execution, InterpCall fallback |
| Pattern Matching | ✅ | All pattern types (79 BDD tests) |
| Where Clauses | ✅ | Generic trait bounds (`where T: Clone + Default`) |
| Default Trait Methods | ✅ | Traits can have default implementations |
| `dyn Trait` Syntax | ✅ | Dynamic trait objects (parsing complete) |
| Mock Library | ✅ | Full mock/spy support with matchers |
| CLI Test Runner | ✅ | `simple test` with JSON/doc formatters |
| Channels | ✅ | Send/recv/try_recv with timeout |
| Generators | ✅ | State machine codegen with slots |
| Futures | ✅ | Eager execution with body outlining |
| Executor | ✅ | Threaded and manual modes |

---

## In Progress Features

### Core Language

| Feature | Status | Notes |
|---------|--------|-------|
| Type Inference (HM) | ✅ | Unification, 68 tests, pipeline integrated |
| Associated Types | ✅ | Parser complete, 5 tests pass |
| Traits - Dynamic Dispatch | ✅ | Full TraitObject coercion + 4 tests pass |

### Memory & Pointers ✅

All pointer types implemented and tested (17 tests pass):
- Unique Pointers (&T) ✅
- Shared Pointers (*T) ✅
- Weak Pointers (-T) ✅
- Handle Pointers (+T) ✅
- Borrows (&x, &mut x) ✅

### Unit Types ✅

| Feature | Status | Notes |
|---------|--------|-------|
| Numeric Units | ✅ | `_km`, `_bytes` suffixes, runtime Value::Unit (9 tests) |
| String Units | ✅ | `"value"_ip` suffixes with Value::Unit |
| Custom Units | ✅ | `unit UserId: u64 as uid` parsing |
| Unit Methods | ✅ | `.value()`, `.suffix()`, `.to_string()` (4 tests) |
| Unit Families | ✅ | `unit length(base: f64): m = 1.0, km = 1000.0` (5 tests) |
| Unit Conversion | ✅ | `.to_X()` methods with factor conversion (14 tests) |
| Type-safe Arithmetic | ✅ | `allow add/sub/mul/div/neg` rules, prevents km + hr (16 tests) |
| Compound Units | 🔄 | Parser complete, `unit velocity = length / time` |

---

## Extended Features

### Unit Types (#200-209)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #200 | Numeric units | ✅ | `_km`, `_hr`, `_bytes` suffixes (14 tests) |
| #201 | Unit families | ✅ | Family definitions with conversion factors |
| #202 | String units | ✅ | `"127.0.0.1"_ip`, `"foo"_regex` suffixes |
| #203 | Type-safe arithmetic | ✅ | `allow add/sub/mul/div/neg` rules with default-allow for ad-hoc units (8 parser + 8 runtime tests) |
| #204 | Unit conversion | ✅ | `.to_X()` methods with factor conversion |
| #205 | Custom units | ✅ | `unit UserId: u64 as uid` parsing |
| #206 | Compound units | ✅ | `unit velocity = length / time` with dimensional analysis (6 tests) |
| #207 | SI prefixes | 📋 | kilo, mega, giga auto-detection |
| #208 | Unit inference | 📋 | Infer units from context |
| #209 | Unit assertions | 📋 | Compile-time unit checking |

### Networking (#210-215)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #210 | TCP sockets | 📋 | Client/server connections |
| #211 | UDP sockets | 📋 | Datagram communication |
| #212 | HTTP client | 📋 | GET/POST/PUT/DELETE |
| #213 | HTTP server | 📋 | Request handling |
| #214 | WebSocket | 📋 | Full-duplex communication |
| #215 | TLS/SSL | 📋 | Encrypted connections |

---

## Advanced Features

### Effect System (#320-325)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #320 | Effect annotations | 📋 | `fn foo() -> T ! IO` |
| #321 | Effect inference | 📋 | Automatic effect detection |
| #322 | Effect handlers | 📋 | Algebraic effect handlers |
| #323 | Effect composition | 📋 | Combining effects |
| #324 | Pure functions | 📋 | Effect-free functions |
| #325 | Capability-based | 📋 | Effect-as-capability |

### GPU & SIMD (#400-410)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #400 | SIMD vectors | 📋 | `vec[4, f32]` types |
| #401 | Vector operations | 📋 | add, mul, dot, cross |
| #402 | Lane operations | 📋 | shuffle, extract, insert |
| #403 | Horizontal ops | 📋 | sum, min, max across lanes |
| #404 | Mask operations | 📋 | Conditional SIMD |
| #405 | GPU kernels | 📋 | `#[gpu]` attribute |
| #406 | Thread blocks | 📋 | Grid/block dimensions |
| #407 | Shared memory | 📋 | Block-local memory |
| #408 | Synchronization | 📋 | Barriers, atomics |
| #409 | Memory coalescing | 📋 | Aligned access patterns |
| #410 | Compute shaders | 📋 | General-purpose GPU |

### UI Framework (#500-505)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #500 | .sui file format | 📋 | UI definition files |
| #501 | Component model | 📋 | Reusable UI elements |
| #502 | State management | 📋 | Reactive updates |
| #503 | Layout system | 📋 | Flexbox-like layout |
| #504 | TUI renderer | 📋 | Terminal UI |
| #505 | GUI renderer | 📋 | Native windows |

### Web Framework (#520-536)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #520 | Routing | 📋 | URL to handler mapping |
| #521 | Controllers | 📋 | Request handlers |
| #522 | Middleware | 📋 | Request/response pipeline |
| #523 | Templates | 📋 | HTML generation |
| #524 | Static files | 📋 | Asset serving |
| #525 | Sessions | 📋 | User state |
| #526 | Authentication | 📋 | Login/logout |
| #527 | Authorization | 📋 | Role-based access |
| #528 | REST API | 📋 | JSON endpoints |
| #529 | GraphQL | 📋 | Query language |
| #530 | WebSocket | 📋 | Real-time updates |
| #531 | SSR | 📋 | Server-side rendering |
| #532 | Database ORM | 📋 | Object-relational mapping |
| #533 | Migrations | 📋 | Schema versioning |
| #534 | Validation | 📋 | Input sanitization |
| #535 | Caching | 📋 | Response caching |
| #536 | Rate limiting | 📋 | Request throttling |

---

## Next Priorities

### Immediate (Sprint)
1. Unique/Shared pointer RAII semantics

### Short Term (Month)
1. Unit conversion methods (#204) - `.to_m()`, `.to_km()`
2. Type-safe unit arithmetic (#203) - Prevent km + hr

### Medium Term (Quarter)
1. GPU kernel basics (#405-409)
2. UI framework prototype (#500-505)
3. Web framework basics (#520-528)

---

## Status Legend

- ✅ **COMPLETE** - Fully implemented and tested
- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet implemented
- 🔮 **FUTURE** - Long-term goal

## Related Documentation

- `feature_done_1.md`: Archived completed features (batch 1)
- `feature_done_2.md`: Archived completed features (batch 2)
- `FEATURE_STATUS.md`: Comprehensive status tracking (211 features)
- `status/*.md`: Individual feature documentation (63+ files)
- `codegen_status.md`: MIR instruction coverage, runtime FFI
- `architecture.md`: Design principles and dependency rules
- `CLAUDE.md`: Development guide for contributors
