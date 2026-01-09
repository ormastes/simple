# Simple Language Features - Archived (Set 7)

**Archive Date:** 2025-12-22
**Total Features:** 138

This file contains completed features extracted from `feature.md` to reduce its size.

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
### SDN - Simple Data Notation (#600-610) ✅

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #600 | SDN Specification | ✅ | - | [spec/sdn.md](../spec/sdn.md) | - | - |
| #601 | SDN Lexer | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/lexer.rs` |
| #602 | SDN Parser | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/parser.rs` |
| #603 | SDN Value Types | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/value.rs` |
| #604 | SDN Document Update | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/document.rs` |
| #605 | SDN CLI | ✅ | R | [spec/sdn.md](../spec/sdn.md) | - | `src/sdn/src/bin/sdn.rs` |
| #606 | Gherkin-Style System Test DSL | ✅ | S+R | [spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md) | `system/gherkin/` | `src/parser/tests/` |
| #607 | `examples` keyword (two-space delimiter) | ✅ | S+R | [spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md) | `system/gherkin/` | `src/parser/tests/` |
| #608 | `feature`/`scenario`/`scenario outline` | ✅ | S+R | [spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md) | `system/gherkin/` | `src/parser/tests/` |
| #609 | Step pattern `<placeholder>` syntax | ✅ | S+R | [spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md) | `system/gherkin/` | `src/parser/tests/` |
| #610 | Doc interpolation `${examples name}` | ✅ | R | [spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md) | `system/gherkin/` | `src/parser/src/ast/tests.rs` |

**Crate:** `src/sdn/` - Standalone library + CLI for config parsing (37 tests)

#### Table Kind Types

| Kind | Syntax | Colon | Delimiter | Use Case |
|------|--------|-------|-----------|----------|
| Typed table | `name: table{i32, i32}` | ✅ | Comma | Strongly-typed SDN data |
| Named table | `name \|f1, f2\|` | ❌ | Comma | SDN configuration |
| Examples table | `examples name:` | ✅ | Two-space | BDD test data (natural language) |

**Grammar:** One-pass LL(2) parseable - see [spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md)

---
### Database & Persistence (#700-713) ✅

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
### Simple Stdlib - Infrastructure APIs (#850-879) ✅

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
### Test Coverage Infrastructure (#920-935) ✅

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

---

---

## Part 2: Issues & Priorities

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
### Architecture Test Library (#936-945) ✅

Static analysis tools for enforcing structural rules and architectural integrity.

**Documentation:**
- [test_guides.md](../guides/test_guides.md) - Architecture test rules
- [test.md](../guides/test.md) - Test execution order

**Extended by:** AOP Architecture Rules (#1026-1035) - adds in-source `forbid`/`allow` rules with unified predicates `pc{...}`

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
### FFI/ABI Interface (#1116-1130) ✅

Stable, explicit foreign function interface for C and Rust interoperability.

**Documentation:**
- [spec/ffi_abi.md](../spec/ffi_abi.md) - FFI/ABI Specification

#### Extern Functions (#1116-1118)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1116 | `extern "C"` function import | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1117 | `extern "Rust"` function import | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1118 | `#[export("C")]` function export | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |

#### Data Layout (#1119-1121)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1119 | `#[repr(C)]` struct layout | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1120 | `#[repr(packed)]` layout | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1121 | `#[repr(align(N))]` layout | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |

#### FFI Types (#1122-1126)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1122 | C string types (CStr, CString) | ✅ | S+R | [ffi_abi.md](../spec/ffi_abi.md) | `std_lib/src/ffi/` | `src/runtime/tests/` |
| #1123 | Raw pointer types (*const, *mut) | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1124 | Ownership annotations (#[borrow], #[owned]) | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1125 | Function pointer types | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1126 | Callback trampolines | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/runtime/tests/` |

#### FFI Infrastructure (#1127-1130)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1127 | `#[link]` library specification | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1128 | Platform-specific ABIs | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1129 | FFI safety lints | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/compiler/tests/` |
| #1130 | `#[catch_panic]` for exports | ✅ | R | [ffi_abi.md](../spec/ffi_abi.md) | - | `src/runtime/tests/` |

---


## Summary

**Total Features Archived:** 138 features
**Feature Ranges:**
- Web Framework: #520-536 (17 features)
- SDN - Simple Data Notation: #600-610 (11 features)
- Database & Persistence: #700-713 (14 features)
- Infrastructure & Dependencies: #825-849 (25 features)
- Simple Stdlib - Infrastructure APIs: #850-879 (30 features)
- Test Coverage Infrastructure: #920-935 (16 features)
- Architecture Test Library: #936-945 (10 features)
- FFI/ABI Interface: #1116-1130 (15 features)

All features marked ✅ Complete and extracted from feature.md on 2025-12-22.
