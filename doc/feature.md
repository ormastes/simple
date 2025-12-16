# Simple Language Features

## Summary Statistics

**Overall Progress:** 59% (125/211 features complete)

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 47 | 38 | 8 | 1 |
| Codegen | 6 | 6 | 0 | 0 |
| Testing & CLI | 39 | 39 | 0 | 0 |
| Concurrency Runtime | 33 | 33 | 0 | 0 |
| Units | 10 | 0 | 0 | 10 |
| Networking | 6 | 0 | 0 | 6 |
| Contracts | 32 | 9 | 1 | 22 |
| Effects | 6 | 0 | 0 | 6 |
| UI Framework | 6 | 0 | 0 | 6 |
| Web Framework | 17 | 0 | 0 | 17 |
| GPU/SIMD | 11 | 0 | 0 | 11 |

**Completed features:**
- [feature_done_1.md](feature_done_1.md) - Archive 1
- [feature_done_2.md](feature_done_2.md) - Archive 2

---

## Importance & Difficulty Legend

**Importance:**
- **High (H)**: Core functionality, blocks other features, or critical for usability
- **Medium (M)**: Important but not blocking, enhances developer experience
- **Low (L)**: Nice-to-have, convenience features, edge cases

**Difficulty:**
- **1**: Trivial (< 1 hour, simple change)
- **2**: Easy (1-4 hours, straightforward)
- **3**: Medium (1-2 days, some complexity)
- **4**: Hard (3-5 days, significant work)
- **5**: Very Hard (1+ weeks, major effort)

---

## In Progress Features

### Core Language

| Feature | Importance | Difficulty | Status | Notes |
|---------|------------|------------|--------|-------|
| **Type Inference (HM)** | H | 5 | 🔄 | Full AST integration pending |
| **Traits** | H | 4 | 🔄 | Parser done, dynamic dispatch pending |
| **Codegen** | H | 5 | 🔄 | Cranelift + LLVM, Interpreter fallback |

### Pointers

| Feature | Importance | Difficulty | Status | Notes |
|---------|------------|------------|--------|-------|
| **Unique Pointers** (&T) | H | 4 | 🔄 | Runtime ✅, Parser/codegen ✅ |
| **Shared Pointers** (*T) | H | 4 | 🔄 | Runtime ✅, Parser/codegen ✅ |
| **Weak Pointers** (-T) | M | 3 | 🔄 | Runtime ✅, Parser/codegen ✅ |
| **Handle Pointers** (+T) | M | 3 | 📋 | Pool-managed handles |

### Concurrency

| Feature | Importance | Difficulty | Status | Notes |
|---------|------------|------------|--------|-------|
| **Actors** | H | 4 | 🔄 | Runtime done, body outlining pending |
| **Futures** | H | 4 | 🔄 | Runtime done, lazy execution pending |

### Codegen

*All codegen features complete - see feature_done_2.md*

---

## Planned Features

### Unit Types (#200-209)

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| #200 | Network Size Units | M | 2 | 📋 | KB, MB, GB, etc. |
| #201 | File System Units | M | 2 | 📋 | Paths, sizes |
| #202 | String Suffix Literals | L | 2 | 📋 | `100_KB` syntax |
| #203 | Time Duration Units | M | 2 | 📋 | ms, s, min, hr |
| #204 | Memory Size Units | M | 2 | 📋 | Bytes, KiB, MiB |
| #205 | Angle Units | L | 2 | 📋 | Degrees, radians |
| #206 | Temperature Units | L | 2 | 📋 | Celsius, Fahrenheit |
| #207 | Distance Units | L | 2 | 📋 | Meters, feet |
| #208 | Currency Units | L | 3 | 📋 | USD, EUR with conversion |
| #209 | Custom Unit Definitions | M | 3 | 📋 | User-defined units |

### Networking (#210-215)

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| #210 | TCP Networking | H | 4 | 📋 | TCP client/server |
| #211 | UDP Networking | M | 3 | 📋 | UDP sockets |
| #212 | HTTP Client | H | 4 | 📋 | HTTP requests |
| #213 | HTTP Server | H | 5 | 📋 | Web server |
| #214 | FTP Client | L | 3 | 📋 | FTP operations |
| #215 | WebSocket | M | 4 | 📋 | WebSocket support |

---

## Contract Features

### In Progress

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-005 | `old(expr)` snapshots | H | 3 | 🔄 | Capture values at function entry |

### Type and Class Invariants

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-010 | Type `invariant:` block | H | 4 | 📋 | Class/struct-level invariants |
| CTR-011 | Entry/exit invariant checking | H | 3 | 📋 | Check on public method boundaries |
| CTR-012 | Module boundary checking | M | 3 | 📋 | Check when values cross API boundaries |

### Refinement Types

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-020 | `where` clause | H | 4 | 📋 | Attach predicates to base types |
| CTR-021 | Subtype relationships | H | 4 | 📋 | `T where P` is subtype of `T` |
| CTR-022 | Compile-time proof | M | 5 | 📋 | Constant folding, range propagation |
| CTR-023 | Runtime fallback | M | 3 | 📋 | Insert checks when proof fails |

### Purity Constraints

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-030 | Pure expression enforcement | M | 3 | 📋 | Contract expressions must be pure |
| CTR-031 | `@pure` function annotation | M | 2 | 📋 | Mark functions callable in contracts |
| CTR-032 | Impure call detection | M | 3 | 📋 | Compile error for impure calls |

### Build Modes

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-040 | `--contracts=off` | H | 2 | 📋 | No checks emitted |
| CTR-041 | `--contracts=boundary` | H | 3 | 📋 | Checks for public/exported only |
| CTR-042 | `--contracts=on` | H | 2 | 📋 | All contract checks |
| CTR-043 | `--contracts=test` | M | 2 | 📋 | Rich diagnostics mode |

### Contract Violations

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-050 | `ContractViolation.Pre` | M | 2 | 📋 | Precondition failure |
| CTR-051 | `ContractViolation.Post` | M | 2 | 📋 | Postcondition failure |
| CTR-052 | `ContractViolation.ErrPost` | M | 2 | 📋 | Error postcondition failure |
| CTR-053 | `ContractViolation.InvariantEntry` | M | 2 | 📋 | Invariant failure at entry |
| CTR-054 | `ContractViolation.InvariantExit` | M | 2 | 📋 | Invariant failure at exit |

### Snapshot-Safe Types

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| CTR-060 | Primitive snapshot | M | 2 | 📋 | i64, bool, enums in old() |
| CTR-061 | Immutable struct snapshot | M | 3 | 📋 | Value structs in old() |
| CTR-062 | `@snapshot` annotation | L | 3 | 📋 | Custom snapshot semantics |

---

## Effects & Capabilities (#410-415)

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| #410 | Capability-Based Imports | H | 5 | 📋 | Effect tracking |
| #411 | IO Effect | H | 3 | 📋 | File/network capability |
| #412 | Async Effect | H | 3 | 📋 | Async/await capability |
| #413 | Unsafe Effect | M | 3 | 📋 | Raw pointer operations |
| #414 | Effect Polymorphism | M | 4 | 📋 | Generic effect handling |
| #415 | Effect Inference | M | 4 | 📋 | Automatic effect tracking |

---

## UI Framework (#510-512)

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| #510 | .sui File Format | M | 4 | 📋 | UI definition files |
| #511 | GUI Renderer | M | 5 | 📋 | Desktop GUI backend |
| #512 | TUI Renderer | M | 4 | 📋 | Terminal UI backend |
| #513 | Component System | M | 4 | 📋 | Reusable UI components |
| #514 | State Management | M | 4 | 📋 | Reactive UI state |
| #515 | Event Handling | M | 3 | 📋 | User input events |

---

## Web Framework (#520-536)

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| #520 | Router | H | 3 | 📋 | URL routing |
| #521 | Controllers | H | 3 | 📋 | Request handlers |
| #522 | Views/Templates | H | 4 | 📋 | HTML templating |
| #523 | Server-Side Rendering | M | 4 | 📋 | SSR support |
| #524 | Middleware | M | 3 | 📋 | Request/response pipeline |
| #525 | Sessions | M | 3 | 📋 | Session management |
| #526 | Authentication | M | 4 | 📋 | Auth system |
| #527 | Database ORM | M | 5 | 📋 | Object-relational mapping |
| #528 | Migrations | M | 3 | 📋 | Schema migrations |
| #529 | Form Handling | M | 3 | 📋 | Form validation |
| #530 | File Uploads | L | 3 | 📋 | Multipart uploads |
| #531 | Static Files | L | 2 | 📋 | Static file serving |
| #532 | JSON API | H | 3 | 📋 | REST API support |
| #533 | GraphQL | M | 4 | 📋 | GraphQL support |
| #534 | WebSocket Server | M | 4 | 📋 | Real-time communication |
| #535 | Rate Limiting | L | 2 | 📋 | Request throttling |
| #536 | CORS | L | 2 | 📋 | Cross-origin support |

---

## GPU & SIMD (#440-450)

| Feature ID | Feature | Importance | Difficulty | Status | Description |
|------------|---------|------------|------------|--------|-------------|
| #440 | GPU Kernels | M | 5 | 📋 | #[gpu] attribute |
| #441 | CUDA Backend | M | 5 | 📋 | NVIDIA GPU support |
| #442 | Vulkan Compute | M | 5 | 📋 | Cross-platform GPU |
| #443 | Metal Backend | L | 5 | 📋 | Apple GPU support |
| #444 | SIMD Intrinsics | H | 4 | 📋 | Vector operations |
| #445 | Auto-Vectorization | M | 5 | 📋 | Automatic SIMD |
| #446 | GPU Memory Management | M | 4 | 📋 | Device memory |
| #447 | Tensor Operations | M | 4 | 📋 | Matrix/tensor math |
| #448 | GPU Synchronization | M | 4 | 📋 | Barriers/fences |
| #449 | Shared Memory | M | 4 | 📋 | GPU shared memory |
| #450 | Warp/Wave Operations | L | 4 | 📋 | SIMT primitives |

---

## Next Priorities

### Immediate (Sprint) - High Importance

| Priority | Feature | Importance | Difficulty | Notes |
|----------|---------|------------|------------|-------|
| 1 | Type Inference full AST integration | H | 5 | Core type safety |
| 2 | Trait dynamic dispatch | H | 4 | Enables polymorphism |
| 3 | Union types | H | 4 | Enables Result/Option |

### Short Term (Month)

| Priority | Feature | Importance | Difficulty | Notes |
|----------|---------|------------|------------|-------|
| 1 | Result/Option types | H | 3 | Depends on unions |
| 2 | Handle pointers (+T) | M | 3 | Pool-managed memory |
| 3 | Bitfields | M | 3 | Hardware/FFI support |
| 4 | TCP Networking (#210) | H | 4 | Basic networking |
| 5 | HTTP Client (#212) | H | 4 | Web requests |

### Medium Term (Quarter)

| Priority | Feature | Importance | Difficulty | Notes |
|----------|---------|------------|------------|-------|
| 1 | Type invariants (CTR-010) | H | 4 | Design by Contract |
| 2 | Refinement types (CTR-020) | H | 4 | Static verification |
| 3 | HTTP Server (#213) | H | 5 | Web server |
| 4 | Capability-based imports (#410) | H | 5 | Effect system |

---

## Status Legend

- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet implemented
- 🔮 **FUTURE** - Long-term goal

## Related Documentation

- `feature_done_1.md`: Archived completed features (batch 1)
- `feature_done_2.md`: Archived completed features (batch 2)
- `FEATURE_STATUS.md`: Comprehensive status tracking (212 features)
- `status/*.md`: Individual feature documentation (63 files)
- `codegen_status.md`: MIR instruction coverage, runtime FFI
- `design/type_system_features.md`: Type system design TODOs
- `CLAUDE.md`: Development guide for contributors
