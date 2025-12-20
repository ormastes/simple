# Simple Language Features

**Last Updated:** 2025-12-20

## Feature Table Format

All feature tables use this standardized 7-column format:

```markdown
| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #NNN | Name | ✅/📋 | R/S/S+R | [doc](path) | `path/` | `path/` |
```

**Column Reference:**

| Column | Description | Example Values |
|--------|-------------|----------------|
| **Feature ID** | Unique identifier (`#NNN`) | `#100`, `#700` |
| **Feature** | Short feature name | `TCP sockets`, `PostgreSQL driver` |
| **Status** | `✅` Complete, `📋` Planned | |
| **Impl** | Implementation: `R` Rust, `S` Simple, `S+R` Both | |
| **Doc** | Link to spec/design doc, or `-` | `[spec/types.md](spec/types.md)` |
| **S-Test** | Simple test path, or `-` | `std_lib/test/unit/net/` |
| **R-Test** | Rust test path, or `-` | `src/runtime/tests/` |

---

## Feature ID Ranges

| Range | Category | Status |
|-------|----------|--------|
| #1-#9 | Infrastructure (Lexer, Parser, AST, HIR, MIR, GC, Pkg, SMF) | ✅ Complete |
| #10-#24 | Core Language (Types, Functions, Structs, Actors, Async) | ✅ Complete |
| #25-#29 | Memory & Pointers | ✅ Complete |
| #30-#49 | Type Inference, Associated Types, Effects | ✅ Complete |
| #50-#56 | Union Types | ✅ Complete |
| #60-#66 | Async State Machine | ✅ Complete |
| #70-#74 | Interpreter Enhancements | ✅ Complete |
| #95-#103 | Codegen (Outlining, Generators, LLVM) | ✅ Complete |
| #110-#157 | Concurrency (Channels, Generators, Executor, Actors, Futures) | ✅ Complete |
| #160-#172 | Pattern Matching | ✅ Complete |
| #180-#197 | Testing - BDD & Doctest | ✅ Complete |
| #200-#217 | Unit Types | ✅ Complete |
| #220-#225 | Networking | ✅ Complete |
| #230-#241 | Mock Library | ✅ Complete |
| #250-#258 | CLI Features | ✅ Complete |
| #300-#311 | GPU/SIMD | ✅ Complete |
| #400-#406 | Contracts | ✅ Complete |
| #510-#519 | UI Framework | ✅ Complete |
| #520-#536 | Web Framework | ✅ Complete (17/17) |
| #600-#610 | SDN + Gherkin DSL | ✅ Complete (11/11) |
| #700-#713 | Database & Persistence (DB + SQP) | ✅ Complete (14/14) |
| #800-#824 | Build & Linker Optimization | 🔄 In Progress (23/25) |
| #825-#849 | Infrastructure & Dependencies | ✅ Complete |
| #850-#879 | Simple Stdlib - Infra APIs | ✅ Complete (30/30) |
| #880-#919 | LLM-Friendly Features | 📋 Planned |
| #920-#935 | Test Coverage Infrastructure | ✅ Complete |
| #936-#945 | Architecture Test Library | ✅ Complete |
| #950-#970 | Formal Verification | ✅ Complete |
| #980-#999 | Code Quality & Documentation | ✅ Complete |

---

## Summary Statistics

**Overall Progress:** 99% (268/269 features complete)

| Category | Total | Complete | Planned |
|----------|-------|----------|---------|
| Core Language | 47 | 47 | 0 |
| Codegen | 5 | 5 | 0 |
| Testing & CLI | 4 | 4 | 0 |
| Concurrency Runtime | 4 | 4 | 0 |
| Contracts | 6 | 6 | 0 |
| Extended - Units | 16 | 16 | 0 |
| Extended - Networking | 6 | 6 | 0 |
| Advanced - Effects | 6 | 6 | 0 |
| Advanced - UI | 3 | 3 | 0 |
| Advanced - GPU/SIMD | 19 | 19 | 0 |
| **SDN + Gherkin DSL** | 11 | 11 | 0 |
| **Database & Persistence** | 14 | 14 | 0 |
| **Web Framework** | 17 | 17 | 0 |
| **Build & Linker Optimization** | 25 | 23 | 2 |
| **Infrastructure & Dependencies** | 25 | 25 | 0 |
| **Simple Stdlib - Infra APIs** | 30 | 30 | 0 |
| **LLM-Friendly Features** | 40 | 0 | 40 |
| **Test Coverage Infrastructure** | 16 | 16 | 0 |
| **Architecture Test Library** | 10 | 10 | 0 |
| **Module Privacy** | 2 | 2 | 0 |

**Test Status:** 1089+ tests passing

**Completed Features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md), [feature_done_3.md](feature_done_3.md), [feature_done_4.md](feature_done_4.md)

---

## Planned Features

### SDN - Simple Data Notation (#600-610)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #600 | SDN Specification | ✅ | - | [spec/sdn.md](../spec/sdn.md) | - | - |
| #601 | SDN Lexer | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/lexer.rs` |
| #602 | SDN Parser | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/parser.rs` |
| #603 | SDN Value Types | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/value.rs` |
| #604 | SDN Document Update | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/document.rs` |
| #605 | SDN CLI | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/bin/sdn.rs` |
| #606 | Gherkin-Style System Test DSL | ✅ | S+R | [spec/gherkin_dsl.md](../spec/gherkin_dsl.md) | `system/gherkin/` | `src/parser/tests/` |
| #607 | `examples` keyword (two-space delimiter) | ✅ | S+R | [spec/gherkin_dsl.md](../spec/gherkin_dsl.md) | `system/gherkin/` | `src/parser/tests/` |
| #608 | `feature`/`scenario`/`scenario outline` | ✅ | S+R | [spec/gherkin_dsl.md](../spec/gherkin_dsl.md) | `system/gherkin/` | `src/parser/tests/` |
| #609 | Step pattern `<placeholder>` syntax | ✅ | S+R | [spec/gherkin_dsl.md](../spec/gherkin_dsl.md) | `system/gherkin/` | `src/parser/tests/` |
| #610 | Doc interpolation `${examples name}` | ✅ | R | [spec/gherkin_dsl.md](../spec/gherkin_dsl.md) | `system/gherkin/` | `src/parser/src/ast/tests.rs` |

**Crate:** `src/sdn/` - Standalone library + CLI for config parsing (37 tests)

#### Table Kind Types

| Kind | Syntax | Colon | Delimiter | Use Case |
|------|--------|-------|-----------|----------|
| Typed table | `name: table{i32, i32}` | ✅ | Comma | Strongly-typed SDN data |
| Named table | `name \|f1, f2\|` | ❌ | Comma | SDN configuration |
| Examples table | `examples name:` | ✅ | Two-space | BDD test data (natural language) |

**Grammar:** One-pass LL(2) parseable - see [spec/gherkin_dsl.md](../spec/gherkin_dsl.md)

---

### Database & Persistence (#700-713) 📋

Database abstraction layer (DB) and query DSL (SQP) for Simple language.

**Documentation:**
- [db.md](./db.md) - Database Abstraction Layer
- [sqp.md](./sqp.md) - Simple Query and Persistence

#### DB Layer - Backend Abstraction (#700-706)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #700 | PostgreSQL driver | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |
| #701 | libSQL driver | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |
| #702 | libSQL Remote (Turso) | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |
| #703 | Connection pooling | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |
| #704 | Transaction API | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |
| #705 | Type mapping | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |
| #706 | Schema introspection | ✅ | R | [db.md](db.md) | - | `src/db/tests/` |

**Architecture:**
```
┌─────────────────────────────────────────────────────────┐
│                    SQP Layer                             │
│   (Query DSL, Data Models, Migrations, Relations)       │
├─────────────────────────────────────────────────────────┤
│                    DB Layer                              │
│   (Unified Interface - Backend Agnostic)                │
├──────────────────────┬──────────────────────────────────┤
│   PostgreSQL Driver  │     libSQL Driver                │
└──────────────────────┴──────────────────────────────────┘
```

#### SQP Layer - Query DSL (#707-713)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #707 | Casual mode | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/src/model.rs` |
| #708 | Formal mode | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/src/model.rs` |
| #709 | Query DSL | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/tests/` |
| #710 | Relations | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/src/model.rs` |
| #711 | Migrations | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/src/migration.rs` |
| #712 | Eager loading | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/src/preload.rs` |
| #713 | Raw SQL escape | ✅ | R | [sqp.md](sqp.md) | - | `src/sqp/tests/` |

**Example (Casual Mode):**
```simple
data User:
    name: str
    email: str unique
    posts: [Post]      # has_many inferred

data Post:
    title: str
    author: User       # belongs_to inferred

# Query DSL
let users = User.where(active: true)
               .order(name: asc)
               .limit(10)
```

---

### Web Framework (#520-536) ✅

SSR-first web framework building on existing UI framework and TCP networking.

**Documentation:** [spec/web.md](../spec/web.md)
**Location:** `simple/std_lib/src/web/`

#### HTTP Core (#520-524)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #520 | HTTP Request Parser | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/http/request.spl` |
| #521 | HTTP Response Builder | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/http/response.spl` |
| #522 | HTTP Server Loop | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/http/server.spl` |
| #523 | SSR Renderer Integration | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/ssr.spl` |
| #524 | Content-Type Detection | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/static.spl` |

#### Routing (#525-529)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #525 | Path Router | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/router.spl` |
| #526 | Route Parameters | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/router.spl` |
| #527 | Route Groups | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/router.spl` |
| #528 | Static File Serving | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/static.spl` |
| #529 | Error Pages | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/http/response.spl` |

#### WebApp Builder (#530-536)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #530 | WebApp Builder | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/app.spl` |
| #531 | Middleware Pipeline | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/middleware.spl` |
| #532 | Logger Middleware | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/middleware.spl` |
| #533 | CORS Middleware | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/middleware.spl` |
| #534 | Handler Context | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/router.spl` |
| #535 | Rate Limit Middleware | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/middleware.spl` |
| #536 | Auth Middleware | ✅ | S | [spec/web.md](../spec/web.md) | - | `std_lib/src/web/middleware.spl` |

**Example Usage:**
```simple
use web.*
use ui.*

async fn home_handler(ctx: Context) -> HttpResponse:
    let tree = ElementTree::new(ElementKind::Main)
    tree.root_mut()
        .with_class("container")
        .with_child(Element::heading(1, "Welcome"))

    return render_to_response(&tree, "Home")

async fn main() -> i32:
    let app = WebApp::new()
        .port(3000)
        .use_logger()
        .use_cors()
        .get("/", home_handler)
        .get("/users/:id", user_handler)
        .static_files("/assets", "public/")

    await app.run()?
    return 0
```

**Architecture:**
```
HTTP Request → HttpServer → Router → Handler → UI Tree → HtmlRenderer → HTTP Response
                   ↓
              Middleware
           (Logger, CORS, RateLimit, Auth)
```

---

### Build & Linker Optimization (#800-824) 📋

Mold-inspired compilation pipeline optimizations for faster builds.

**Documentation:**
- [mold_linker_analysis.md](./research/mold_linker_analysis.md) - Mold linker integration analysis
- [src_to_bin_optimization.md](./research/src_to_bin_optimization.md) - Full pipeline optimization guide

#### Mold Linker Integration (#800-805)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #800 | Mold detection | ✅ | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/compiler/src/linker/native.rs` |
| #801 | `--linker` CLI flag | ✅ | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/driver/src/main.rs` |
| #802 | LLVM backend integration | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/compiler/tests/` |
| #803 | Fallback to lld | ✅ | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/compiler/src/linker/native.rs` |
| #804 | Symbol analysis | ✅ | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/compiler/src/linker/analysis.rs` |
| #805 | RISC-V 32-bit cross-compile | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/linker/tests/` |

**Implemented Features:**
- `NativeLinker` enum with Mold/Lld/Ld variants (`src/compiler/src/linker/native.rs`)
- Auto-detection with fallback chain: mold → lld → ld
- `LinkerBuilder` fluent API for configuration
- `LinkOptions` for library linking, stripping, PIE, shared libs
- `LinkerError` types with symbol extraction from error messages
- CLI: `simple linkers` command to list available linkers
- CLI: `--linker <name>` flag for explicit linker selection
- Environment: `SIMPLE_LINKER`, `SIMPLE_LINKER_THREADS`, `SIMPLE_LINKER_DEBUG`

**Expected Impact:** 4x faster native linking, 35% faster native builds

#### Parallelization (#806-812)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #806 | Parallel file parsing | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/parallel.rs` |
| #807 | Parallel HIR lowering | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/hir/lower/parallel.rs` |
| #808 | Parallel monomorphization | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/monomorphize/parallel.rs` |
| #809 | Parallel MIR lowering | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/mir/parallel.rs` |
| #810 | Parallel codegen | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/codegen/parallel.rs` |
| #811 | Parallel SMF linking | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/linker/parallel.rs` |
| #812 | Pipeline parallelism | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/pipeline_parallel.rs` |

**Expected Impact:** 8-10x speedup for 10+ file projects

#### String Interning (#813-815)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #813 | Parser string interning | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/src/interner.rs` |
| #814 | Linker symbol interning | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/linker/interner.rs` |
| #815 | Hash precomputation | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/linker/interner.rs` |

**Expected Impact:** 25% speedup, 67% memory reduction for strings

#### Memory Optimization (#816-820)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #816 | AST arena allocation | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/src/arena.rs` |
| #817 | HIR arena allocation | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/hir/arena.rs` |
| #818 | MIR arena allocation | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/mir/arena.rs` |
| #819 | Code buffer pooling | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/codegen/buffer_pool.rs` |
| #820 | Memory-mapped file reading | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/common/src/file_reader.rs` |

**Expected Impact:** 36% memory reduction, 15% speedup

#### Caching (#821-824)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #821 | Monomorphization cache | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/monomorphize/cache.rs` |
| #822 | Effect analysis cache | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/effects_cache.rs` |
| #823 | Incremental compilation | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/src/incremental.rs` |
| #824 | `--parallel` / `--profile` flags | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/driver/src/compile_options.rs` |

**Expected Impact:** 3x speedup for incremental builds

**Projected Overall Impact:**
- Single-file: 2.3x faster (2100ms → 917ms)
- Multi-file (10 files): 10.2x faster (21s → 2s)

---

### Infrastructure & Dependencies (#825-849) ✅

Low-level infrastructure changes: allocators, threading primitives, hashing, and data structures.

**Status:** All 25 features complete - workspace dependencies added to Cargo.toml files.

#### Allocators (#825-827)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #825 | jemalloc integration | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `Cargo.toml` |
| #826 | mimalloc integration | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `Cargo.toml` |
| #827 | Allocator selection | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `Cargo.toml` |

**Crates:** `tikv-jemallocator`, `mimalloc`
**Impact:** Better scaling beyond 4-8 cores, reduced lock contention

#### Threading & Concurrency (#828-832)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #828 | rayon thread pool | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/Cargo.toml` |
| #829 | DashMap concurrent map | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/Cargo.toml` |
| #830 | crossbeam utilities | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/Cargo.toml` |
| #831 | parking_lot locks | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/Cargo.toml` |
| #832 | Thread-local storage | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/Cargo.toml` |

**Crates:** `rayon`, `dashmap`, `crossbeam`, `parking_lot`
**Note:** Rust equivalents of Intel TBB concurrent containers

#### Atomic Primitives (#833-835)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #833 | Atomic flags | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `crossbeam` |
| #834 | AtomicU64 counters | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `crossbeam` |
| #835 | Compare-and-swap ops | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `crossbeam` |

**Crates:** `std::sync::atomic`, `crossbeam-utils`
**Impact:** Enable true parallelism without serializing locks

#### Hashing Libraries (#836-839)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #836 | SHA-1 hashing | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/loader/Cargo.toml` |
| #837 | xxHash fast hashing | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/loader/Cargo.toml` |
| #838 | AHash default hasher | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/Cargo.toml` |
| #839 | Hash trait interface | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/common/Cargo.toml` |

**Crates:** `sha1`, `xxhash-rust`, `ahash`
**Impact:** 20-30% faster symbol resolution with better hash functions

#### Data Structures (#840-845)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #840 | typed-arena allocator | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/Cargo.toml` |
| #841 | bumpalo allocator | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `Cargo.toml` |
| #842 | lasso string interner | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/Cargo.toml` |
| #843 | SmallVec optimization | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/Cargo.toml` |
| #844 | IndexMap ordered map | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/Cargo.toml` |
| #845 | BitVec bit arrays | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `Cargo.toml` |

**Crates:** `typed-arena`, `bumpalo`, `lasso`, `smallvec`, `indexmap`, `bitvec`
**Impact:** 36% memory reduction, better cache locality

#### I/O & Serialization (#846-849)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #846 | memmap2 file mapping | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/loader/Cargo.toml` |
| #847 | bincode serialization | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/loader/Cargo.toml` |
| #848 | serde derive | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `Cargo.toml` |
| #849 | Streaming I/O | ✅ | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `memmap2` |

**Crates:** `memmap2`, `bincode`, `serde`
**Impact:** 15% faster I/O for large files

**Cargo.toml Changes Required:**
```toml
[workspace.dependencies]
# Allocators
tikv-jemallocator = { version = "0.5", optional = true }
mimalloc = { version = "0.1", optional = true }

# Threading
rayon = "1.10"
dashmap = "6.0"
crossbeam = "0.8"
parking_lot = "0.12"

# Hashing
sha1 = "0.10"
xxhash-rust = { version = "0.8", features = ["xxh3"] }
ahash = "0.8"

# Data Structures
typed-arena = "2.0"
bumpalo = "3.14"
lasso = { version = "0.7", features = ["multi-threaded"] }
smallvec = "1.13"
indexmap = "2.2"
bitvec = "1.0"

# I/O
memmap2 = "0.9"
bincode = "1.3"
serde = { version = "1.0", features = ["derive"] }
```

---

### Simple Stdlib - Infrastructure APIs (#850-879) 📋

Simple language interfaces and implementations exposing infrastructure capabilities to user programs.

**Location:** `simple/std_lib/src/infra/`

#### Allocator Interface (#850-853)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #850 | `trait Allocator` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/alloc.spl` |
| #851 | `Arena[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/alloc.spl` |
| #852 | `Pool[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/alloc.spl` |
| #853 | `@allocator` decorator | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/alloc.spl` |

**Example:**
```simple
use infra.alloc.*

# Arena for batch allocations
let arena = Arena[Node].new(capacity: 1000)
let node1 = arena.alloc(Node(value: 1))
let node2 = arena.alloc(Node(value: 2))
arena.reset()  # Free all at once

# Object pool with reuse
let pool = Pool[Buffer].new(size: 64, capacity: 100)
let buf = pool.acquire()
buf.write("data")
pool.release(buf)  # Return for reuse

# Custom allocator for class
@allocator(Arena)
class TreeNode:
    value: i64
    left: TreeNode?
    right: TreeNode?
```

#### Concurrent Collections (#854-859)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #854 | `ConcurrentMap[K, V]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/concurrent.spl` |
| #855 | `ConcurrentSet[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/concurrent.spl` |
| #856 | `ConcurrentQueue[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/concurrent.spl` |
| #857 | `ConcurrentStack[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/concurrent.spl` |
| #858 | `ConcurrentVec[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/concurrent.spl` |
| #859 | `ShardedMap[K, V]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/concurrent.spl` |

**Example:**
```simple
use infra.concurrent.*

let map = ConcurrentMap[str, i64].new()

# Safe concurrent access from multiple actors
actor Worker(id: i64, map: ConcurrentMap[str, i64]):
    fn run():
        map.insert(f"key_{id}", id * 10)
        let value = map.get(f"key_{id}")

# Parallel iteration
map.par_iter().for_each(|k, v| print(f"{k}: {v}"))
```

#### Atomic Types (#860-864)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #860 | `Atomic[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/atomic.spl` |
| #861 | `AtomicBool` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/atomic.spl` |
| #862 | `AtomicInt` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/atomic.spl` |
| #863 | `AtomicRef[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/atomic.spl` |
| #864 | `AtomicFlag` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/atomic.spl` |

**Example:**
```simple
use infra.atomic.*

let counter = AtomicInt.new(0)
let flag = AtomicFlag.new()

# Lock-free increment
let old = counter.fetch_add(1, ordering: SeqCst)

# Compare-and-swap
let success = counter.compare_exchange(
    expected: 5,
    desired: 10,
    success_order: SeqCst,
    failure_order: Relaxed
)

# Spin-lock pattern
while flag.test_and_set(ordering: Acquire):
    hint.spin_loop()
# Critical section
flag.clear(ordering: Release)
```

#### Hash Interface (#865-869)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #865 | `trait Hasher` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/hash.spl` |
| #866 | `Sha1Hasher` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/hash.spl` |
| #867 | `Sha256Hasher` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/hash.spl` |
| #868 | `XxHasher` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/hash.spl` |
| #869 | `@hash_with` decorator | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/hash.spl` |

**Example:**
```simple
use infra.hash.*

# Trait definition
trait Hasher:
    fn write(data: [u8]) -> Self
    fn finish() -> u64
    fn reset()

# Use different hashers
let sha1 = Sha1Hasher.new()
sha1.write(b"hello")
let digest = sha1.finish_bytes()  # [u8; 20]

let xx = XxHasher.new()
xx.write(b"hello")
let hash = xx.finish()  # u64

# Custom hasher for Map
@hash_with(XxHasher)
let fast_map = Map[str, i64].new()
```

#### Parallel Iterators (#870-874)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #870 | `trait ParIter[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/parallel.spl` |
| #871 | `.par_map()` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/parallel.spl` |
| #872 | `.par_filter()` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/parallel.spl` |
| #873 | `.par_reduce()` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/parallel.spl` |
| #874 | `.par_for_each()` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/parallel.spl` |

**Example:**
```simple
use infra.parallel.*

let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

# Parallel map (uses all CPU cores)
let squared = data.par_map(|x| x * x)

# Parallel filter
let evens = data.par_filter(|x| x % 2 == 0)

# Parallel reduce
let sum = data.par_reduce(0, |acc, x| acc + x)

# Parallel for_each with chunking
data.par_for_each(chunk_size: 100, |x|
    expensive_operation(x)
)

# Chained parallel operations
let result = data
    .par_filter(|x| x > 5)
    .par_map(|x| x * 2)
    .par_reduce(0, |a, b| a + b)
```

#### Synchronization Primitives (#875-879)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #875 | `Mutex[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/sync.spl` |
| #876 | `RwLock[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/sync.spl` |
| #877 | `Once` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/sync.spl` |
| #878 | `Lazy[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/sync.spl` |
| #879 | `ThreadLocal[T]` | ✅ | S | [spec/stdlib.md](spec/stdlib.md) | - | `std_lib/src/infra/sync.spl` |

**Example:**
```simple
use infra.sync.*

# Mutex for exclusive access
let mutex = Mutex[List[i64]].new([])
mutex.lock(|list|
    list.push(42)
)

# RwLock for read-heavy workloads
let cache = RwLock[Map[str, Data]].new(Map.new())
cache.read(|c| c.get("key"))      # Multiple readers OK
cache.write(|c| c.insert("key", data))  # Exclusive write

# Lazy initialization
let config = Lazy[Config].new(|| load_config())
let c = config.get()  # Initializes on first access

# Thread-local storage
let tls = ThreadLocal[Buffer].new(|| Buffer.new(1024))
let buf = tls.get()  # Per-thread buffer
```

---

### LLM-Friendly Features (#880-919) 📋

Features to make Simple optimized for LLM-assisted development, verification, and collaboration.

**Documentation:**
- [llm_friendly.md](./llm_friendly.md) - LLM Quality Contract
- [plans/llm_friendly.md](./plans/llm_friendly.md) - Implementation Plan

#### Capability-Based Effects (#880-884)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #880 | `module requires[cap]` | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #881 | `@pure` / `@io` / `@net` | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #882 | Capability propagation | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #883 | Forbidden effect errors | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #884 | Stdlib effect annotations | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/effects/` | - |

**Example:**
```simple
module app.domain requires[pure]:
    # Only pure functions - no I/O allowed
    use core.math.*     # OK
    use io.fs.*         # ERROR: fs capability not declared

@io @net
fn fetch_and_save(url: str, path: str):
    let data = http.get(url)?   # Requires @net
    fs.write(path, data)?       # Requires @io
```

#### AST/IR Export (#885-889)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #885 | `--emit-ast` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #886 | `--emit-hir` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #887 | `--emit-mir` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #888 | `--error-format=json` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #889 | Semantic diff tool | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Example:**
```bash
simple compile app.spl --emit-ast > ast.json
simple compile app.spl --error-format=json 2> errors.json
simple diff --semantic old.spl new.spl
```

#### Context Pack Generator (#890-893)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #890 | `simple context` command | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #891 | Dependency symbol extraction | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #892 | Markdown context format | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #893 | JSON context format | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Example:**
```bash
# Extract minimal context (only symbols used by app.service)
simple context app.service --format=markdown > context.md
simple context app.service --format=json > context.json
```

**Impact:** 90% reduction in LLM context tokens

#### Property-Based Testing (#894-898)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #894 | `@property_test` decorator | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | `src/compiler/tests/` |
| #895 | Input generators | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |
| #896 | Shrinking on failure | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | `src/runtime/tests/` |
| #897 | Configurable iterations | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |
| #898 | Generator combinators | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |

**Example:**
```simple
use testing.property.*

@property_test(iterations: 1000)
fn test_sort_idempotent(input: [i64]):
    expect(sort(sort(input))).to_equal(sort(input))

@property_test
fn test_reverse_reverse(input: [i64]):
    expect(reverse(reverse(input))).to_equal(input)
```

#### Snapshot/Golden Tests (#899-902)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #899 | `@snapshot_test` decorator | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/snapshot/` | `src/compiler/tests/` |
| #900 | Snapshot storage | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #901 | `--snapshot-update` flag | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #902 | Multi-format snapshots | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/snapshot/` | `src/driver/tests/` |

**Example:**
```simple
@snapshot_test
fn test_render_user_json():
    let user = User(id: 42, name: "Alice")
    let json = render_json(user)
    expect_snapshot(json, format: "json")
```

#### Lint Framework (#903-907)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #903 | Lint rule trait | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/lint/` | - |
| #904 | Built-in rules | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #905 | Configurable severity | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #906 | `simple lint` command | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #907 | Auto-fix suggestions | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Configuration (`simple.toml`):**
```toml
[lint]
unchecked_indexing = "deny"
global_mutable_state = "deny"
magic_numbers = "warn"

[lint.rules]
max_function_length = 50
max_nesting_depth = 4
```

#### Canonical Formatter (#908-910)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #908 | `simple fmt` command | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #909 | Single correct style | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/parser/tests/` |
| #910 | Format-on-save integration | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |

**Impact:** Eliminates stylistic variance; LLM output is predictable

#### Build & Audit Infrastructure (#911-915)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #911 | Deterministic build mode | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #912 | Replay logs | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #913 | `@generated_by` provenance | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/audit/` | `src/compiler/tests/` |
| #914 | API surface lock file | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #915 | Spec coverage metric | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |

**Example:**
```simple
# Auto-generated provenance annotation
@generated_by(tool: "claude", prompt_hash: "abc123", version: "3.5")
fn calculate_tax(amount: i64) -> i64:
    ...
```

#### Sandboxed Execution (#916-919)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #916 | Resource limits | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #917 | Network isolation | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #918 | Filesystem isolation | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #919 | `simple run --sandbox` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Impact:** Safely verify LLM-generated code without risk

**Projected Benefits:**
- LLM error rate: <5% contract violations
- Context size: 90% reduction with context packs
- Edge case coverage: 80%+ with property tests
- Reproducibility: 100% deterministic builds

---

### Test Coverage Infrastructure (#920-935) 📋

Coverage tools and metrics for different test levels (System, Service, Integration).

**Documentation:**
- [test.md](../guides/test.md) - Test policy and coverage metrics
- [test_guides.md](../guides/test_guides.md) - Test hierarchy and rules

#### Coverage Types by Test Level (#920-926)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #920 | System Test: Public interface class touch | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #921 | Service Test: Interface class touch | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #922 | Service Test: External lib touch | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #923 | Integration Test: Public interface function touch | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #924 | Integration Test: Neighbor package touch | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #925 | Unit Test: Branch/Condition coverage | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/tests/` |
| #926 | Merged coverage report (all levels) | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/tests/` |

**Coverage Metrics by Test Level:**
```
+------------------------------------------------------------------+
| Test Level   | Coverage Metric           | Threshold | Status    |
+------------------------------------------------------------------+
| System       | Public interface class    | 100%      | ✅ Done    |
| Service      | Interface + Ext lib touch | 100%      | ✅ Done    |
| Integration  | Public func + Neighbor    | 100%      | ✅ Done    |
| Unit         | Branch/Condition          | 100%      | ✅ Done    |
+------------------------------------------------------------------+
```

#### Coverage Tool Enhancements (#927-932)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #927 | `public_api.yml` interface section | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage.rs` |
| #928 | `public_api.yml` external_libs section | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage.rs` |
| #929 | `public_api.yml` neighbors section | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage.rs` |
| #930 | `coverage_gen service` report type | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/bin/coverage_gen.rs` |
| #931 | `make coverage-service` target | ✅ | R | [test.md](../guides/test.md) | - | `Makefile` |
| #932 | Class touch coverage report | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |

#### Coverage Report Outputs (#933-935)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #933 | `coverage_system.json` (class touch) | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #934 | `coverage_service.json` (interface + ext) | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |
| #935 | `coverage_integration.json` (func + neighbor) | ✅ | R | [test.md](../guides/test.md) | - | `src/util/simple_mock_helper/src/coverage_extended.rs` |

**public_api.yml Extended Schema:**
```yaml
# System Test: Public interface class touch
public_classes:
  simple_compiler:
    - CompilerPipeline
    - Codegen
    - MirLowerer
  simple_driver:
    - Runner
    - Interpreter

# Service Test: Interface classes (trait implementors)
interfaces:
  simple_common:
    - DynLoader
    - DynModule
  simple_loader:
    - MemoryAllocator

# Service Test: External library touch points
external_libs:
  cranelift: [codegen, frontend, module]
  abfall: [GcRuntime]
  tracing: [info, debug, error]

# Integration Test: Neighbor package touch
neighbors:
  simple_compiler:
    depends_on: [simple_parser, simple_runtime, simple_common]
  simple_driver:
    depends_on: [simple_compiler, simple_loader, simple_runtime]

# Integration Test: Public functions (existing)
public_functions:
  simple_compiler:
    - CompilerPipeline::new
    - CompilerPipeline::compile
  # ...

# System Test: Types with methods (existing)
types:
  simple_compiler::CompilerPipeline:
    methods: [new, with_gc, compile]
  # ...
```

---

### Architecture Test Library (#936-945)

Static analysis tools for enforcing structural rules and architectural integrity.

**Documentation:**
- [test_guides.md](../guides/test_guides.md) - Architecture test rules
- [test.md](../guides/test.md) - Test execution order

#### Architecture Validation Rules (#936-940)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #936 | No mock in production code check | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/util/arch_test/` |
| #937 | Layer dependency validation | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/util/arch_test/` |
| #938 | Circular dependency detection | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/dependency_tracker/src/graph.rs` |
| #939 | Interface contract verification | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/util/arch_test/` |
| #940 | Skip-layer connection prevention | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/util/arch_test/` |

**Architecture Test Rules:**
```
+---------------------------------------------------------------+
| RULE                                  | ENFORCEMENT            |
+---------------------------------------------------------------+
| No mocks in production implementation | Static analysis        |
| Proper layer connections only         | Dependency check       |
| Interface contracts respected         | Contract verification  |
| No circular dependencies              | Graph analysis         |
| No skip-layer connections             | Layer validation       |
+---------------------------------------------------------------+
```

#### Architecture Test Library API (#941-945)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #941 | `arch_test` crate with validation API | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/util/arch_test/` |
| #942 | `@arch_test` decorator for test functions | ✅ | S | [test_guides.md](../guides/test_guides.md) | `std_lib/test/system/spec/arch_spec.spl` | - |
| #943 | Layer definition DSL | ✅ | S | [test_guides.md](../guides/test_guides.md) | `std_lib/test/system/spec/arch_spec.spl` | - |
| #944 | Dependency graph visualization | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | `src/util/arch_test/tests/` |
| #945 | `make arch-test` target | ✅ | R | [test_guides.md](../guides/test_guides.md) | - | - |

**Usage Example:**
```spl
# test/arch/layer_rules_spec.spl

use arch_test.*

@arch_test
describe "Layer Architecture":
    layers:
        presentation: ["app/controllers/*", "app/ui/*"]
        business: ["app/services/*", "app/logic/*"]
        data: ["app/models/*", "app/repos/*"]

    it "presentation layer only accesses business layer":
        layer("presentation")
            .may_only_access("business")
            .check()

    it "business layer does not access presentation":
        layer("business")
            .must_not_access("presentation")
            .check()

    it "no circular dependencies":
        all_layers()
            .must_be_acyclic()
            .check()

    it "no mocks in production code":
        source("app/**/*.spl")
            .must_not_contain("@mock")
            .check()
```

---

### Module Privacy & Explicit Proxying (#48-49) ✅

When `__init__.spl` is present, child directories are private by default and require explicit proxying.

**Documentation:**
- [spec/modules.md](../spec/modules.md) - Module system specification

#### Module Privacy Features (#48-49)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #48 | `__init__.spl` child directory access prevention | ✅ | R | [spec/modules.md](../spec/modules.md) | - | `src/compiler/src/module_resolver.rs` |
| #49 | Explicit proxy exports in `__init__.spl` | ✅ | R | [spec/modules.md](../spec/modules.md) | - | `src/compiler/src/module_resolver.rs` |

**Module Privacy Rules:**
```
+------------------------------------------------------------------+
| RULE                                  | BEHAVIOR                  |
+------------------------------------------------------------------+
| __init__.spl present                  | Children are PRIVATE      |
| No __init__.spl                       | Children are PUBLIC       |
| Child access without proxy            | Compile ERROR             |
| Explicit proxy via `pub use`          | Child becomes PUBLIC      |
+------------------------------------------------------------------+
```

**Directory Structure Example:**
```
mypackage/
├── __init__.spl          # Makes children private
├── public_api.spl        # Explicitly exported via __init__.spl
├── internal/             # PRIVATE - no direct access allowed
│   ├── __init__.spl      # Also makes its children private
│   ├── helper.spl        # Private to internal/
│   └── utils.spl         # Private to internal/
└── models/               # PRIVATE unless proxied
    └── user.spl
```

**`__init__.spl` Explicit Proxying:**
```spl
# mypackage/__init__.spl

mod mypackage

# Explicit public exports (proxy)
pub use public_api.*           # Makes public_api.spl contents public
pub use models.User            # Exports only User from models/

# Private - NOT exported (no pub)
use internal.*                 # Internal use only

# Re-export with rename
pub use models.UserProfile as Profile
```

**Access Rules:**
```spl
# ALLOWED - explicitly proxied
use mypackage.public_api.MyClass    # ✓ proxied via pub use
use mypackage.User                  # ✓ proxied via pub use

# FORBIDDEN - child not proxied
use mypackage.internal.helper       # ✗ Error: internal is private
use mypackage.models.user.UserData  # ✗ Error: UserData not exported
```

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
1. ~~SDN implementation (#601-605)~~ ✅ Complete
2. Database layer basics (#700-706)

### Medium Term (Quarter)
1. SQP query DSL (#707-713)
2. ~~Web framework basics (#520-536)~~ ✅ Complete

---

## Status Legend

- ✅ **COMPLETE** - Fully implemented and tested
- 📋 **PLANNED** - Designed, not yet implemented

---

## Related Documentation

- [feature_done_1.md](feature_done_1.md) - Archive 1: Infrastructure, Core Language
- [feature_done_2.md](feature_done_2.md) - Archive 2: Codegen, Concurrency, Contracts
- [feature_done_3.md](feature_done_3.md) - Archive 3: UI, Union Types, GPU/SIMD
- [feature_done_4.md](feature_done_4.md) - Archive 4: DB/SQP design, consolidated
- [db.md](db.md) - Database Abstraction Layer
- [sqp.md](sqp.md) - Simple Query and Persistence DSL
- [research/mold_linker_analysis.md](research/mold_linker_analysis.md) - Mold linker integration analysis
- [research/src_to_bin_optimization.md](research/src_to_bin_optimization.md) - Pipeline optimization guide
- [llm_friendly.md](llm_friendly.md) - LLM Quality Contract
- [plans/llm_friendly.md](plans/llm_friendly.md) - LLM-Friendly Implementation Plan
- [codegen_status.md](codegen_status.md) - MIR instruction coverage
- [architecture.md](architecture.md) - Design principles
- [CLAUDE.md](../CLAUDE.md) - Development guide
