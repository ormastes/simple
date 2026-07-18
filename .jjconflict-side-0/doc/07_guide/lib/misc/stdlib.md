# Standard Library Guide

Covers SDN format, string utilities, database access (DB + SQP), and atomic text databases.

---

## Runtime intrinsics (`rt_*`) are internal — use std aliases

`rt_*` functions are **runtime intrinsics**: the low-level bridge between Simple and
the native runtime. They are **not part of the application API**. App and library
developers must **never** declare `extern fn rt_*` or call `rt_*` directly — use the
**std aliases** (thin wrappers) instead:

| Instead of raw `rt_*` | Use the std alias |
|------------------------|-------------------|
| `rt_file_read_text(p)` | `std.io_runtime.file_read(p)` (returns `text`, `""` if missing) |
| `rt_file_write_text(p, c)` | `std.io_runtime.file_write(p, c)` |
| `rt_file_exists(p)` | `std.io_runtime.file_exists(p)` |
| `rt_env_get(k)` | `std.io_runtime.env_get(k)` |
| `rt_process_run(cmd, args)` | `std.io_runtime.process_run(...)` / `shell(...)` |
| `rt_process_spawn_async(cmd, args)` | `app.io.mod.process_spawn_async(cmd, args)` |
| `rt_process_spawn_async(cmd, args, env)` | `app.io.mod.process_spawn_async_env(cmd, args, env)` |
| `rt_process_wait(pid, ms)` | `app.io.mod.process_wait(pid, ms)` |
| `rt_process_is_running(pid)` | `app.io.mod.process_is_running(pid)` |
| `rt_process_is_alive(pid)` | `app.io.mod.process_is_alive(pid)` |
| `rt_process_kill(pid)` | `app.io.mod.process_kill(pid)` |
| `rt_cli_get_args()` | `std.io_runtime.get_args()` |
| `rt_getpid()` | `std.io_runtime.getpid()` |
| `rt_dir_list(p)` | `std.io_runtime.dir_list(p)` |

```simple
# WRONG — app code must not touch rt_* directly
extern fn rt_file_read_text(path: text) -> text
val c = rt_file_read_text("x.txt") ?? ""

# RIGHT — use the std alias
use std.io_runtime.{file_read}
val c = file_read("x.txt")
```

**Why:** intrinsics are unstable, backend-specific, and some are unimplemented in a
given backend (calling a spec-less pointer-returning `rt_*` can even crash — see
`doc/08_tracking/bug/interp_missing_pointer_extern_nil_deref_sigsegv_2026-06-18.md`).
The std aliases are stable, documented, and backed by registered intrinsics.

**Enforcement:** the compiler's `raw_rt_access` lint (RAW-RT-001, default *warn*)
flags any `extern fn rt_*` declared outside the privileged tiers (`src/lib`,
`src/runtime`, `src/compiler`). Genuinely low-level modules (emulators, baremetal
MMIO, crypto/protocol implementations) may opt out with a file-level
`@runtime_intrinsics` / `#[runtime_intrinsics]` marker. See `doc/07_guide/app/lint.md`.

---

## SDN (Simple Data Notation)

SDN is Simple's native configuration format, replacing TOML. It is 30-50% more token-efficient and integrates natively with Simple tooling.

### Syntax

```sdn
# Comments start with #

# Key-value pairs
name: my-project
version: 1.0.0
enabled: true
count: 42
ratio: 3.14

# Arrays
features: [auth, logging, metrics]

# Nested objects
server:
  database:
    host: localhost
    port: 5432

# Tables (structured data)
users |id, name, role|
  1, Alice, admin
  2, Bob, user
```

### Package Manifest (simple.sdn)

```sdn
package:
  name: my-project
  version: 1.0.0
  license: MIT
  description: A useful library

dependencies:
  http: 2.0
  json:
    version: 1.5
    features: [serde]
```

### Migration from TOML

| TOML | SDN |
|------|-----|
| `[section]` | `section:` |
| `key = "value"` | `key: value` |
| `[section.nested]` | Indented under parent |
| `features = ["a", "b"]` | `features: [a, b]` |

Both formats are supported during transition. `simple.sdn` is checked first; `simple.toml` is a fallback.

```bash
# Verify SDN works
simple check
simple test --list
```

---

## String Core Module

**Module:** `std.text_core`

### Basic Operations

```simple
use std.text_core.{str_len, str_concat, str_eq}

str_len("hello")              # 5
str_concat("hello", " world") # "hello world"
str_eq("test", "test")        # true
```

### Slicing and Access

```simple
use std.text_core.{str_slice, str_char_at, str_safe_slice}

str_slice("hello", 0, 3)       # "hel"
str_char_at("hello", 1)        # "e"
str_char_at("hello", 99)       # "" (safe, returns empty)
str_safe_slice("hi", -1, 100)  # "hi" (bounds-safe)
```

### Search

```simple
use std.text_core.{str_contains, str_starts_with, str_ends_with}
use std.text_core.{str_index_of, str_last_index_of}

str_contains("hello world", "world")  # true
str_index_of("hello", "l")            # 2
str_last_index_of("hello", "l")       # 3
str_index_of("hello", "x")            # -1
```

### Trimming, Replacement, Split/Join

```simple
use std.text_core.{str_trim, str_replace_all, str_split, str_join}

str_trim("  hello  ")                  # "hello"
str_replace_all("hello", "l", "L")    # "heLLo"
str_split("a,b,c", ",")               # ["a", "b", "c"]
str_join(["x", "y", "z"], "-")        # "x-y-z"
```

### Case Conversion and Manipulation

```simple
use std.text_core.{str_to_lower, str_to_upper, str_capitalize}
use std.text_core.{str_reverse, str_repeat, str_pad_left}

str_to_lower("HELLO")      # "hello"
str_to_upper("hello")      # "HELLO"
str_capitalize("hello")    # "Hello"
str_reverse("hello")       # "olleh"
str_repeat("ab", 3)        # "ababab"
str_pad_left("42", 5, "0") # "00042"
```

**Note:** Case conversion is ASCII only (A-Z, a-z). Use intermediate `var` instead of chained method calls (runtime limitation).

### When to Use Which Module

| Need | Module |
|------|--------|
| Basic string ops (length, concat, trim, split) | `std.text_core` |
| ASCII lookup, platform newlines, hashing | `std.text` |
| HTML/URL/JS/CSS escaping, hex conversion | `std.template.utilities` |

---

## Concurrency Primitives

Simple has distinct APIs for OS threads, cooperative green threads, pool-backed
tasks, and channels. Use the API name when searching the codebase; searching only
for `fiber` or scheduler runtime terms can miss the implemented stdlib module.

| Need | API | Implementation | Notes |
|------|-----|----------------|-------|
| Spawn a platform thread | `std.concurrent.thread.{thread_spawn}` | `src/lib/nogc_async_mut/concurrent/thread.spl` / `thread_sffi.spl` | Uses OS threads (`pthread_create` / `CreateThread`) |
| Schedule lightweight cooperative work | `std.concurrent.cooperative_green.{cooperative_green_spawn, cooperative_green_spawn_value, cooperative_green_run_one, cooperative_green_run_all}` | `src/lib/nogc_async_mut/concurrent/cooperative_green.spl` over `green_thread.spl` | Runs queued work/results on the current OS thread; no preemption or CPU parallelism |
| Coordinate logical green tasks | `std.concurrent.green_channel.{green_channel_new, green_channel_recv, green_channel_send}` | `src/lib/nogc_async_mut/concurrent/green_channel.spl` | Pure Simple nonblocking channel contract; empty recv parks a logical green task, send unparks a waiter, bounded full send reports backpressure |
| Schedule bounded CPU-parallel value work | `std.concurrent.multicore_green.{multicore_green_spawn, multicore_green_spawn_sliced, multicore_green_safepoint, multicore_green_set_parallelism, multicore_green_parallelism}` / `MulticoreGreenHandle.used_runtime_pool()` / `MulticoreGreenHandle.ran_inline_fallback()` / `MulticoreGreenSlicedHandle.used_runtime_pool()` / `MulticoreGreenSlicedHandle.ran_inline_fallback()` / `MulticoreGreenSliceResult` / `multicore_green_{submitted,completed,pending,busy,blocked}_count()` | `src/lib/nogc_async_mut/concurrent/multicore_green.spl` | Pure Simple facade over runtime-seed `rt_pool_submit` / `rt_pool_join` / `rt_pool_is_done` support; profile rows require runtime-pool acceptance and treat inline fallback as non-M:N. Set parallelism before the first spawn for a Go `GOMAXPROCS`-like hosted pool limit. Counter helpers are scheduler evidence for submitted/completed progress and queue/worker state; they are not automatic preemption evidence. Use `multicore_green_spawn_sliced` when a long task can expose scalar progress state and yield fairness by requeueing between slices. Use `multicore_green_safepoint()` only as an explicit runtime/compiler poll hook inside long hosted workers; it may grow compensation capacity and yield the current OS worker, but it is not automatic ordinary-closure preemption. Live pools can grow but plain closures do not claim shrink/preemption behavior yet. |
| Reuse a worker pool | `task_spawn` / `TaskHandle` | `src/lib/nogc_async_mut/thread_pool.spl` | Lower-level task API that reuses `multicore_green_spawn` for runtime-pool execution and inline fallback. Current cross-language M:N profile rows use `multicore_green_spawn` directly so profile evidence stays tied to `used_runtime_pool()` and public multicore-green counters. |
| Send values between concurrent work | `std.concurrent.channel.{channel_new, channel_from_id}` | `src/lib/nogc_sync_mut/concurrent/channel.spl` | Runtime MPMC channel surface |
| Cancel async work cooperatively | `std.async.cancellation.{CancellationToken}` | `src/lib/nogc_async_mut/async/cancellation.spl` | Token registry with child-token propagation; poll `is_cancelled()` inside tasks |
| Mutual exclusion / limits in async code | `std.async.sync.{AsyncMutex, AsyncSemaphore}` | `src/lib/nogc_async_mut/async/sync.spl` | Non-blocking acquire/release for single-carrier async; not OS-thread-safe |
| Async delays / deadlines | `std.async.timer.{TimerFuture}` | `src/lib/nogc_async_mut/async/timer.spl` | Polls against `current_time_ms`; pair with the poll-once `timeout` combinator |

Green tasks are **share-nothing** (enforced by `simple check` as `E-PAR-006`): a
`green_spawn`, `cooperative_green_spawn`, or `multicore_green_spawn` closure must
not read module-level mutable `var`s or write captured `var`s. Inline
`multicore_green_spawn_sliced` step lambdas follow the same rule. Pass inputs as
locals captured by value and communicate via return values,
`MulticoreGreenSliceResult` state, or `green_channel`. `thread_spawn` is exempt
because OS threads may share through Mutex.

### Coroutine & Process Lifecycle Hardening

Coroutines and cooperative green tasks are non-preemptive stackless state
machines. New or changed coroutine features need SPipe checks for resume
ordering, completion/join behavior, and post-completion idempotence. A test that
only observes the first resume is not enough for a lifecycle claim.

Starvation or fairness claims require the concurrency/resource model gate, or an
explicit release blocker that says the claim is not proven. Do not promote a
single interleaving, host-only simulator run, or generated artifact into a
stronger baremetal scheduling claim.

Any `process_spawn_async` or `process_spawn_async_env` path must assert cleanup
through `process_wait`, `process_is_running`/`process_is_alive`, or
`process_kill`. Lifecycle evidence must call the `app.io.mod.process_*`
facades; raw `rt_process_*` only proves runtime-owner behavior. A spawned
process without an observed wait, liveness check, or kill path is incomplete
evidence.

OS thread lifecycle evidence must prove a spawned `ThreadHandle` reaches a
terminal state through `join()` or `free()`. Repeated terminal cleanup must stay
a safe no-op instead of turning into a double-free or blocked join.

### Green Thread Example

```simple
use std.concurrent.cooperative_green.{cooperative_green_spawn, cooperative_green_run_all}

fn value_7() -> i64:
    7

fn main():
    val handle = cooperative_green_spawn(value_7)
    cooperative_green_run_all()
    print handle.join()
```

`cooperative_green_spawn` is useful for cooperative scheduling semantics and
low-overhead queued work, but it is not a Go-goroutine equivalent. It does not
run tasks in parallel and cannot preempt a long-running closure. The profile
lane now uses the direct `cooperative_green_spawn` surface again after the
compiled SMF/native cooperative regressions were closed in
`doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md`, and
the green/cooperative SSpec runner mismatch is closed in
`doc/08_tracking/bug/green_thread_spec_runner_mismatch_2026-06-11.md`.
`cooperative_green_spawn_value` remains available when a caller already has a
computed result instead of a closure. For Go-like CPU-parallel benchmarks, use
`multicore_green_spawn` as the current profile row. Use the lower-level
pool-backed `task_spawn` path only when the test explicitly targets the task
API itself, or use future scheduler-aware green-thread work when that lands.

### Multicore Green Example

```simple
use std.concurrent.multicore_green.{
    multicore_green_parallelism,
    multicore_green_safepoint,
    multicore_green_set_parallelism,
    multicore_green_spawn,
    multicore_green_spawn_sliced,
    MulticoreGreenSliceResult,
}

fn value_9() -> i64:
    9

fn count_step(state: i64) -> MulticoreGreenSliceResult:
    if state >= 10:
        return MulticoreGreenSliceResult.completed(state)
    return MulticoreGreenSliceResult.continue_with(state + 1)

fn main():
    multicore_green_set_parallelism(2)
    val handle = multicore_green_spawn(\: value_9())
    print handle.join()
    print handle.used_runtime_pool()
    print multicore_green_parallelism()

    val sliced = multicore_green_spawn_sliced(0, count_step)
    print sliced.used_runtime_pool()
    print sliced.join()
```

`multicore_green_spawn` is the current Pure Simple API used by the
cross-language profile for bounded CPU-parallel value tasks. It keeps the public
surface distinct from `cooperative_green_spawn` so cooperative scheduling tests do not
pretend to be Go-style M:N scheduling. The `rt_pool_*` calls are runtime-seed
support behind that facade, not a combined Pure Simple user-facing API. Use
`handle.used_runtime_pool()` when a
test or benchmark must prove that work was accepted by the bounded runtime pool;
use `handle.ran_inline_fallback()` only for interpreter or platform fallback
coverage. Profile evidence should call `multicore_green_set_parallelism(workers)`
before the first spawn, record `multicore_green_parallelism()`, and compare
against Go rows whose `GOMAXPROCS` is pinned to the same `CPU_WORKERS` value.
`multicore_green_spawn_sliced(initial_state, step_fn)` is the current explicit
hosted fairness API for long Pure Simple work: each step returns
`MulticoreGreenSliceResult.continue_with(next_state)` to requeue itself or
`MulticoreGreenSliceResult.completed(value)` to finish. The API intentionally
uses scalar progress state so it avoids the older captured-mutable-state
closure blocker and does not change the semantics of plain
`multicore_green_spawn` closures. `simple check` rejects
`multicore_green_spawn_sliced` when it is imported from the wrong concurrency
surface (`E-PAR-003`), called without both an integer initial state and a step
function (`E-PAR-004`), or given an inline step lambda that mutates shared state
(`E-PAR-006`).
`multicore_green_safepoint()` is the lower-level explicit poll hook for future
compiler-inserted loop safepoints. A long hosted worker may call it to let the
runtime mark the worker blocked, start compensation capacity, and yield the OS
worker so queued tasks can progress. Do not use it as evidence of automatic
plain-closure preemption, and do not build correctness on its numeric return.

---

## Database Abstraction (DB Layer)

The DB layer provides a backend-agnostic interface for SQL databases. SQP (below) builds on top of it.

```
SQP Layer (Query DSL, Data Models, Migrations)
DB Layer (Unified Interface)
PostgreSQL Driver  |  libSQL Driver
```

### Connecting

```simple
use db.*

val config = DbConfig(
    backend: DbBackend.LibSql,
    connection_string: "file:./data/app.db"
)

val db = Db.connect(config)?
```

**Backends:**

| Backend | Connection String |
|---------|------------------|
| PostgreSQL | `postgres://user:pass@host:5432/dbname` |
| libSQL (local) | `file:./data/app.db` or `:memory:` |
| libSQL (Turso) | `libsql://db-name.turso.io?authToken=...` |

### Queries

```simple
# Execute (INSERT, UPDATE, DELETE)
val result = db.execute(
    "INSERT INTO users (name, email) VALUES (?, ?)",
    ["Alice", "alice@example.com"]
)?
print "Inserted {result.rows_affected} row(s)"

# Query
val users = db.query(
    "SELECT id, name FROM users WHERE active = ?",
    [true]
)?

for row in users:
    val id: i64 = row.get("id")?
    val name: str = row.get("name")?
    print "User {id}: {name}"
```

### Transactions

```simple
with_transaction(db) \tx:
    tx.execute("UPDATE accounts SET balance = balance - ? WHERE id = ?", [100, 1])?
    tx.execute("UPDATE accounts SET balance = balance + ? WHERE id = ?", [100, 2])?
    Ok(())
```

### Type Mapping

| Simple Type | PostgreSQL | libSQL (SQLite) |
|-------------|------------|-----------------|
| `bool` | `BOOLEAN` | `INTEGER` (0/1) |
| `i64` | `BIGINT` | `INTEGER` |
| `f64` | `DOUBLE PRECISION` | `REAL` |
| `str` | `TEXT` | `TEXT` |
| `datetime` | `TIMESTAMPTZ` | `TEXT` (ISO8601) |
| `[u8]` | `BYTEA` | `BLOB` |

### Switching Backends

```simple
# Development
val dev_config = DbConfig(
    backend: DbBackend.LibSql,
    connection_string: "file:./dev.db"
)

# Production
val prod_config = DbConfig(
    backend: DbBackend.Postgres,
    connection_string: "postgres://user:pass@prod-db:5432/app"
)

# Same code works with both
val db = Db.connect(if is_production: prod_config else dev_config)?
```

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `DATABASE_URL` | Connection string | `file:./data/app.db` |
| `DB_BACKEND` | Backend type | `libsql` |
| `DB_POOL_MAX` | Max pool connections | `10` |
| `DB_TIMEOUT_MS` | Connection timeout | `5000` |

---

## SQP (Simple Query and Persistence)

SQP is the high-level query and persistence DSL built on the DB layer.

### Casual Mode (Default)

```simple
data User:
    name: str
    email: str unique
    posts: [Post]          # has_many inferred

data Post:
    title: str
    body: str
    author: User           # belongs_to inferred
    tags: [Tag] many       # many-to-many
```

Auto-generated fields: `id: i64 primary`, `created_at: datetime`, `updated_at: datetime`. Foreign keys inferred from type references.

### Formal Mode

```simple
@table("users")
data User:
    @primary @auto
    id: i64

    @unique @index
    email: str(255)

    @nullable
    bio: str?

    @has_many(Post, foreign: "author_id", cascade: delete)
    posts: [Post]

    @timestamps
```

### Query DSL

```simple
users = User.where(active: true)
            .order(created_at: desc)
            .limit(10)

adults = User.filter \u: u.age >= 18

posts = Post.include(:author, :tags)
            .where(published: true)

# Raw SQL escape hatch
result = db.query "SELECT * FROM users WHERE id = ?", [user_id]
```

### Transactions

```simple
db.transaction \tx:
    val user = User.create(name: "Alice", email: "alice@test.com")
    val post = Post.create(title: "Hello", author: user)
    tx.commit()
```

### Migrations

```simple
# Auto-generated from data definitions
migrate "create_users":
    create_table "users":
        id: i64 primary auto
        name: str(255)
        email: str(255) unique index
        created_at: datetime
        updated_at: datetime
```

---

## Atomic Text Database

**Module:** `std.db_atomic`

Thread-safe, atomic database operations for SDN-formatted text files with file locking, atomic writes, and backup management.

### Basic Operations

```simple
use std.db_atomic.{atomic_read, atomic_write, atomic_update, DbConfig}

# Read
val content = atomic_read("data.sdn", DbConfig.defaults())?

# Write
atomic_write("data.sdn", "new content", DbConfig.defaults())?

# Atomic update (read-modify-write with locking)
atomic_update("data.sdn", |content| {
    content + "\n    new_row, value1, value2"
}, DbConfig.defaults())?
```

### AtomicTable

```simple
use std.db_atomic.{AtomicTable, DbConfig}

# Create table
val table = AtomicTable.create(
    "todos.sdn", "todos",
    ["id", "title", "status"],
    DbConfig.defaults()
)?

# Add row
table.add_row(["1", "Fix bug", "done"])?

# Load existing
val existing = AtomicTable.load("todos.sdn", "todos", DbConfig.defaults())?
```

### Configuration Profiles

| Profile | Lock Timeout | Size Limit | Backups |
|---------|-------------|------------|---------|
| `DbConfig.defaults()` | 10s | 500 MB | 5 kept |
| `DbConfig.no_backups()` | 10s | 500 MB | None |
| `DbConfig.strict()` | 30s | 100 MB | 10 kept |

### Atomic Write Pattern

1. Acquire exclusive file lock
2. Create backup (if configured)
3. Write to temporary file
4. Rename temp to target (atomic)
5. Release lock

### Batch Operations

```simple
# Single lock acquisition for multiple rows
table.update(|content| {
    var new_content = content
    for item in items:
        new_content = new_content + format_row(item)
    new_content
})?
```

---

## SMF note.sdn Metadata

The `note.sdn` section in SMF files tracks generic instantiation metadata for lazy instantiation, circular dependency detection, and hot-reload support.

### Tracking Instantiations

```simple
use simple/compiler/monomorphize/note_sdn.*

var note = NoteSdnMetadata.new()

note.add_instantiation(InstantiationEntry.new(
    template: "List",
    type_args: [ConcreteType.Named("Int", [])],
    mangled_name: "List$Int",
    from_file: "app.spl",
    from_loc: "app.spl:10:5",
    to_obj: "app.o",
    status: InstantiationStatus.Compiled
))

note.add_dependency(DependencyEdge.new(
    from_inst: "List$Int",
    to_inst: "Int",
    dep_kind: DependencyKind.TypeParam
))

val sdn_text = note.to_sdn()
```

### Instantiation Status

| Status | Meaning |
|--------|---------|
| `Compiled` | Compiled to native code |
| `Deferred` | Deferred for lazy compilation |
| `JitCompiled` | JIT-compiled at runtime |

---

## Related Files

- SDN syntax reference: `doc/07_guide/sdn_syntax_guide.md`
- String core: `src/lib/common/string_core.spl`
- DB & SQP: `doc/07_guide/apps/database.md`
- Atomic DB: `src/lib/nogc_sync_mut/db_atomic.spl`
- Note SDN: `src/compiler/40.mono/note_sdn.spl`
