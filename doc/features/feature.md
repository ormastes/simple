# Simple Language Features

**Last Updated:** 2025-12-18

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
| #1-#8 | Infrastructure (Lexer, Parser, AST, HIR, MIR, GC, Pkg) | ✅ Complete |
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
| #510-#524 | UI Framework | ✅ Complete |
| #600-#605 | SDN | 📋 Planned |
| #700-#713 | Database & Persistence (DB + SQP) | 📋 Planned |
| #800-#824 | Build & Linker Optimization | 📋 Planned |
| #825-#849 | Infrastructure & Dependencies | 📋 Planned |
| #850-#879 | Simple Stdlib - Infra APIs | 📋 Planned |
| #880-#919 | LLM-Friendly Features | 📋 Planned |
| #950-#970 | Formal Verification | ✅ Complete |
| #980-#999 | Code Quality & Documentation | ✅ Complete |

---

## Summary Statistics

**Overall Progress:** 48% (123/267 features complete)

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
| **SDN** | 6 | 1 | 5 |
| **Database & Persistence** | 14 | 0 | 14 |
| **Web Framework** | 17 | 0 | 17 |
| **Build & Linker Optimization** | 25 | 0 | 25 |
| **Infrastructure & Dependencies** | 25 | 0 | 25 |
| **Simple Stdlib - Infra APIs** | 30 | 0 | 30 |
| **LLM-Friendly Features** | 40 | 0 | 40 |

**Test Status:** 1089+ tests passing

**Completed Features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md), [feature_done_3.md](feature_done_3.md), [feature_done_4.md](feature_done_4.md)

---

## Planned Features

### SDN - Simple Data Notation (#600-605) 📋

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #600 | SDN Specification | ✅ | - | [spec/sdn.md](spec/sdn.md) | - | - |
| #601 | SDN Lexer | 📋 | R | [spec/sdn.md](spec/sdn.md) | - | `src/sdn/tests/` |
| #602 | SDN Parser | 📋 | R | [spec/sdn.md](spec/sdn.md) | - | `src/sdn/tests/` |
| #603 | SDN Value Types | 📋 | R | [spec/sdn.md](spec/sdn.md) | - | `src/sdn/tests/` |
| #604 | SDN Document Update | 📋 | R | [spec/sdn.md](spec/sdn.md) | - | `src/sdn/tests/` |
| #605 | SDN CLI | 📋 | R | [spec/sdn.md](spec/sdn.md) | `system/sdn/` | `src/sdn/tests/` |

**Crate:** `src/sdn/` - Standalone library + CLI for config parsing

---

### Database & Persistence (#700-713) 📋

Database abstraction layer (DB) and query DSL (SQP) for Simple language.

**Documentation:**
- [db.md](./db.md) - Database Abstraction Layer
- [sqp.md](./sqp.md) - Simple Query and Persistence

#### DB Layer - Backend Abstraction (#700-706)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #700 | PostgreSQL driver | 📋 | R | [db.md](db.md) | - | `src/db/tests/` |
| #701 | libSQL driver | 📋 | R | [db.md](db.md) | - | `src/db/tests/` |
| #702 | libSQL Remote (Turso) | 📋 | R | [db.md](db.md) | - | `src/db/tests/` |
| #703 | Connection pooling | 📋 | R | [db.md](db.md) | - | `src/db/tests/` |
| #704 | Transaction API | 📋 | S+R | [db.md](db.md) | `system/db/` | `src/db/tests/` |
| #705 | Type mapping | 📋 | R | [db.md](db.md) | - | `src/db/tests/` |
| #706 | Schema introspection | 📋 | R | [db.md](db.md) | - | `src/db/tests/` |

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
| #707 | Casual mode | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |
| #708 | Formal mode | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |
| #709 | Query DSL | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |
| #710 | Relations | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |
| #711 | Migrations | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |
| #712 | Eager loading | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |
| #713 | Raw SQL escape | 📋 | S+R | [sqp.md](sqp.md) | `system/sqp/` | `src/sqp/tests/` |

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

### Web Framework (#520-536) 📋

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #520 | Routing | 📋 | S+R | [spec/web.md](spec/web.md) | `system/web/` | `src/web/tests/` |
| #521 | Controllers | 📋 | S | [spec/web.md](spec/web.md) | `system/web/` | - |
| #522 | Middleware | 📋 | S | [spec/web.md](spec/web.md) | `system/web/` | - |
| #523 | Templates | 📋 | S+R | [spec/web.md](spec/web.md) | `system/web/` | `src/web/tests/` |
| #524-528 | Core features | 📋 | S+R | [spec/web.md](spec/web.md) | `system/web/` | `src/web/tests/` |
| #529-536 | Advanced | 📋 | S+R | [spec/web.md](spec/web.md) | `system/web/` | `src/web/tests/` |

---

### Build & Linker Optimization (#800-824) 📋

Mold-inspired compilation pipeline optimizations for faster builds.

**Documentation:**
- [mold_linker_analysis.md](./research/mold_linker_analysis.md) - Mold linker integration analysis
- [src_to_bin_optimization.md](./research/src_to_bin_optimization.md) - Full pipeline optimization guide

#### Mold Linker Integration (#800-805)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #800 | Mold detection | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/linker/tests/` |
| #801 | `--linker` CLI flag | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/driver/tests/` |
| #802 | LLVM backend integration | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/compiler/tests/` |
| #803 | Fallback to lld | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/linker/tests/` |
| #804 | Symbol analysis | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/linker/tests/` |
| #805 | RISC-V 32-bit cross-compile | 📋 | R | [mold_linker_analysis.md](research/mold_linker_analysis.md) | - | `src/linker/tests/` |

**Expected Impact:** 4x faster native linking, 35% faster native builds

#### Parallelization (#806-812)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #806 | Parallel file parsing | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/tests/` |
| #807 | Parallel HIR lowering | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #808 | Parallel monomorphization | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #809 | Parallel MIR lowering | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #810 | Parallel codegen | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #811 | Parallel SMF linking | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/linker/tests/` |
| #812 | Pipeline parallelism | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |

**Expected Impact:** 8-10x speedup for 10+ file projects

#### String Interning (#813-815)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #813 | Parser string interning | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/tests/` |
| #814 | Linker symbol interning | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/linker/tests/` |
| #815 | Hash precomputation | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/linker/tests/` |

**Expected Impact:** 25% speedup, 67% memory reduction for strings

#### Memory Optimization (#816-820)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #816 | AST arena allocation | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/tests/` |
| #817 | HIR arena allocation | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #818 | MIR arena allocation | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #819 | Code buffer pooling | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #820 | Memory-mapped file reading | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/driver/tests/` |

**Expected Impact:** 36% memory reduction, 15% speedup

#### Caching (#821-824)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #821 | Monomorphization cache | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #822 | Effect analysis cache | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #823 | Incremental compilation | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/driver/tests/` |
| #824 | `--parallel` / `--profile` flags | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/driver/tests/` |

**Expected Impact:** 3x speedup for incremental builds

**Projected Overall Impact:**
- Single-file: 2.3x faster (2100ms → 917ms)
- Multi-file (10 files): 10.2x faster (21s → 2s)

---

### Infrastructure & Dependencies (#825-849) 📋

Low-level infrastructure changes: allocators, threading primitives, hashing, and data structures.

#### Allocators (#825-827)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #825 | jemalloc integration | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/tests/` |
| #826 | mimalloc integration | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/tests/` |
| #827 | Allocator selection | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/tests/` |

**Crates:** `tikv-jemallocator`, `mimalloc`
**Impact:** Better scaling beyond 4-8 cores, reduced lock contention

#### Threading & Concurrency (#828-832)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #828 | rayon thread pool | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #829 | DashMap concurrent map | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #830 | crossbeam utilities | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/tests/` |
| #831 | parking_lot locks | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/runtime/tests/` |
| #832 | Thread-local storage | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |

**Crates:** `rayon`, `dashmap`, `crossbeam`, `parking_lot`
**Note:** Rust equivalents of Intel TBB concurrent containers

#### Atomic Primitives (#833-835)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #833 | Atomic flags | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #834 | AtomicU64 counters | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #835 | Compare-and-swap ops | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/linker/tests/` |

**Crates:** `std::sync::atomic`, `crossbeam-utils`
**Impact:** Enable true parallelism without serializing locks

#### Hashing Libraries (#836-839)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #836 | SHA-1 hashing | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/linker/tests/` |
| #837 | xxHash fast hashing | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/linker/tests/` |
| #838 | AHash default hasher | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #839 | Hash trait interface | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/common/tests/` |

**Crates:** `sha1`, `xxhash-rust`, `ahash`
**Impact:** 20-30% faster symbol resolution with better hash functions

#### Data Structures (#840-845)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #840 | typed-arena allocator | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/tests/` |
| #841 | bumpalo allocator | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #842 | lasso string interner | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/parser/tests/` |
| #843 | SmallVec optimization | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #844 | IndexMap ordered map | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #845 | BitVec bit arrays | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |

**Crates:** `typed-arena`, `bumpalo`, `lasso`, `smallvec`, `indexmap`, `bitvec`
**Impact:** 36% memory reduction, better cache locality

#### I/O & Serialization (#846-849)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #846 | memmap2 file mapping | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/loader/tests/` |
| #847 | bincode serialization | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/compiler/tests/` |
| #848 | serde derive | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/pkg/tests/` |
| #849 | Streaming I/O | 📋 | R | [src_to_bin_optimization.md](research/src_to_bin_optimization.md) | - | `src/loader/tests/` |

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
| #850 | `trait Allocator` | 📋 | S | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | - |
| #851 | `Arena[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #852 | `Pool[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #853 | `@allocator` decorator | 📋 | R | [spec/stdlib.md](spec/stdlib.md) | - | `src/compiler/tests/` |

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
| #854 | `ConcurrentMap[K, V]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #855 | `ConcurrentSet[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #856 | `ConcurrentQueue[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #857 | `ConcurrentStack[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #858 | `ConcurrentVec[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #859 | `ShardedMap[K, V]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |

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
| #860 | `Atomic[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #861 | `AtomicBool` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #862 | `AtomicInt` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #863 | `AtomicRef[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #864 | `AtomicFlag` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |

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
| #865 | `trait Hasher` | 📋 | S | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | - |
| #866 | `Sha1Hasher` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #867 | `Sha256Hasher` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #868 | `XxHasher` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #869 | `@hash_with` decorator | 📋 | R | [spec/stdlib.md](spec/stdlib.md) | - | `src/compiler/tests/` |

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
| #870 | `trait ParIter[T]` | 📋 | S | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | - |
| #871 | `.par_map()` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #872 | `.par_filter()` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #873 | `.par_reduce()` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #874 | `.par_for_each()` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |

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
| #875 | `Mutex[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #876 | `RwLock[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #877 | `Once` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #878 | `Lazy[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |
| #879 | `ThreadLocal[T]` | 📋 | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/infra/` | `src/runtime/tests/` |

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
1. SDN implementation (#601-605)
2. Database layer basics (#700-706)

### Medium Term (Quarter)
1. SQP query DSL (#707-713)
2. Web framework basics (#520-536)

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
