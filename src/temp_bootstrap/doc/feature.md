# Simple Language Features

## Summary Statistics

**Overall Progress:** 59% (125/211 features complete)

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 47 | 38 | 8 | 1 |
| Codegen | 6 | 6 | 0 | 0 |
| Testing & CLI | 39 | 39 | 0 | 0 |
| Concurrency Runtime | 33 | 33 | 0 | 0 |
| Contracts | 32 | 9 | 1 | 22 |
| Extended - Units | 10 | 0 | 0 | 10 |
| Extended - Networking | 6 | 0 | 0 | 6 |
| Advanced - Effects | 6 | 0 | 0 | 6 |
| Advanced - UI | 6 | 0 | 0 | 6 |
| Advanced - Web | 17 | 0 | 0 | 17 |
| Advanced - GPU/SIMD | 11 | 0 | 0 | 11 |

**Completed features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md)

---

## Recent Completions (Dec 2025)

| Feature | Status | Description |
|---------|--------|-------------|
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
| Type Inference (HM) | 🔄 | Scaffold complete, AST integration pending |
| Traits - Dynamic Dispatch | 🔄 | Parser ✅, TraitObject runtime pending |
| Union Type Narrowing | 🔄 | Basic support, full flow analysis pending |
| Associated Types | 📋 | Trait-associated type members |

### Memory & Pointers

| Feature | Status | Notes |
|---------|--------|-------|
| Unique Pointers (&T) | 🔄 | Runtime ✅, Parser/codegen ✅ |
| Shared Pointers (*T) | 🔄 | Runtime ✅, Parser/codegen ✅ |
| Weak Pointers (-T) | 🔄 | Runtime ✅, Parser/codegen ✅ |
| Handle Pointers (+T) | 📋 | Pool-managed handles |

### Contracts

| Feature | Status | Notes |
|---------|--------|-------|
| `old(expr)` Snapshots | 🔄 | Parser done, codegen pending |
| Contract Inheritance | 📋 | Subtype contract propagation |

---

## Extended Features

### Unit Types (#200-209)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| #200 | Numeric units | 📋 | `_km`, `_hr`, `_bytes` suffixes |
| #201 | Unit families | 📋 | ByteCount, Duration with conversions |
| #202 | String units | 📋 | `"127.0.0.1"_ip`, `"foo"_regex` |
| #203 | Type-safe arithmetic | 📋 | Prevent km + hr |
| #204 | Unit conversion | 📋 | `to_X()` methods |
| #205 | Custom units | 📋 | User-defined unit types |
| #206 | Compound units | 📋 | m/s, kg*m/s² |
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
1. Complete `dyn Trait` runtime support (TraitObject creation)
2. Finish Type Inference AST integration
3. Unique/Shared pointer RAII semantics

### Short Term (Month)
1. Memory pointer types - Handle pointers
2. Unit type basics (#200-204)
3. Effect system foundation (#320-322)

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
