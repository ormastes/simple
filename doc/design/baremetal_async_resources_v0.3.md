# Simple Bare-Metal Async + Limited Resources v0.3

**Date**: 2026-02-15
**Status**: Design Specification
**Prereqs**: `doc/design/baremetal_features_examples.md`, `src/std/async_core.spl`, `src/std/async_embedded.spl`

---

## 0) Design decisions and fixes from v0.2

### 0.1 Syntax corrections (Simple, not Rust/C)

All examples use Simple syntax: `val`/`var`, `:` blocks, `fn`/`me`, `match`/`case`.
No braces for blocks. No `let`. No `impl Trait for Type` (use `impl Type:` duck typing).

### 0.2 Issues fixed from v0.2 draft

| Issue | v0.2 | v0.3 fix |
|-------|------|----------|
| `trait Limited { }` syntax | Brace-delimited | Colon + indent (Simple trait) |
| `const CAP: Unit` in trait | Not valid Simple | `fn cap() -> i64` required method |
| `let h = ...` in examples | Rust syntax | `val h = ...` |
| `struct { len: u16, data: [u8; 256] }` | Rust struct | `class Packet:` with fields |
| Reserve `take_reserved()` | Undefined semantics | Specified as `pool.take()` with compile-time guarantee |
| `fn leaves() -> List[(ResPath, Unit, CAP)]` | Too abstract | Compiler intrinsic, no user-facing API |
| `task_group` policy unclear | `strict` vs `relaxed` undefined | Concrete spawn-phase rules |
| GC limits `max=1000` syntax | Mixed key-value | SDN config blocks |
| Missing `->` on `async fn` return | `async fn main() -> Never` | `async fn main() -> Never:` |
| `loop { }` in examples | Brace-delimited | `loop:` indent-based |
| No waiter overflow handling | Silent corruption | Compile-time waiter sum check |

### 0.3 Key design principle

> **Static verification means the compiler rejects the program, not that it warns.**
> In strict mode, every capacity violation is a compile error.
> In relaxed mode, violations produce warnings and runtime checks.

---

## 1) Limited trait

### 1.1 Core idea

A "limited resource" has a compile-time known capacity. The compiler tracks
usage statically in baremetal strict mode.

### 1.2 Trait definition

```simple
trait Limited:
    # Unit type for this resource (Slots, Entries, Bytes, Waiters)
    # Represented as a compile-time tag, not a runtime type.
    fn unit_name() -> text
    fn cap() -> i64

trait LimitedComposite:
    # A bundle of multiple limited resources.
    # Compiler enumerates leaf resources by inspecting struct fields.
    # No user-facing method needed; this is a marker trait.
    pass_dn
```

### 1.3 Compiler rules

- Any `resource pool`, `resource queue`, `resource set`, `resource dict` implicitly
  implements `Limited`.
- Any `resource struct` whose **all** leaf fields are `Limited` implicitly implements
  `LimitedComposite`.
- The compiler flattens composite resources into a list of `(path, unit_name, cap)` triples.
  This is a compiler intrinsic, not a function call.

### 1.4 What "Unit" means per resource kind

| Declaration | unit_name | cap value |
|-------------|-----------|-----------|
| `resource pool P: T[N]` | `"Slots"` | N |
| `resource queue Q: Queue<T, N, waiters=W>` | `"Entries"` for storage, `"Waiters"` for waiters | N, W |
| `resource set S: Set<T, N>` | `"Entries"` | N |
| `resource dict D: Dict<K, V, N>` | `"Entries"` | N |

Waiters are a **separate limited leaf** from the queue/event storage.
For `Queue<T, 8, waiters=2>`, the compiler tracks two leaves:
- `Q.entries`: cap=8
- `Q.waiters`: cap=2

---

## 2) Resource declarations

### 2.1 Grammar

```
ResourceDecl :=
    "resource" "pool"   Ident ":" Type "[" IntLit "]" ResourceOpts?
  | "resource" "queue"  Ident ":" "Queue" "<" Type "," IntLit "," "waiters" "=" IntLit ">" ResourceOpts?
  | "resource" "set"    Ident ":" "Set" "<" Type "," IntLit ">" ResourceOpts?
  | "resource" "dict"   Ident ":" "Dict" "<" Type "," Type "," IntLit ">" ResourceOpts?
  | "resource" "struct" Ident ":" Newline Indent ResourceField+ Dedent

ResourceField :=
    Ident ":" ResourceDecl    # nested resource
  | Ident ":" Type "[" IntLit "]"   # inline pool shorthand

ResourceOpts :=
    "@" "section" "(" StringLit ")"   # linker section placement

ResPath := Ident ( "." Ident )*
```

### 2.2 Examples

```simple
# Simple pool
resource pool PktPool: Packet[8]

# Queue with explicit waiter limit
resource queue RxQueue: Queue<Handle<PktPool>, 8, waiters=2>

# Fixed-capacity set
resource set ConnSet: Set<ConnId, 32>

# Fixed-capacity dictionary
resource dict StatsTable: Dict<ConnId, Stats, 64>

# Bundle: composite of multiple resources
resource struct NetRes:
    pkt_pool: Packet[8]
    rxq: Queue<Handle<PktPool>, 8, waiters=2>
    stats: Dict<ConnId, Stats, 64>
```

### 2.3 Compiler expansion of bundles

For `resource struct NetRes`, the compiler generates this leaf table:

| Leaf path | unit_name | cap |
|-----------|-----------|-----|
| `NetRes.pkt_pool` | Slots | 8 |
| `NetRes.rxq.entries` | Entries | 8 |
| `NetRes.rxq.waiters` | Waiters | 2 |
| `NetRes.stats` | Entries | 64 |

---

## 3) Task declarations and reserve

### 3.1 Grammar

```
TaskDecl :=
    TaskAttr* "async" "fn" Ident "(" ParamList? ")" ( "->" Type )? ":" Block

TaskAttr :=
    "@task" "(" TaskArg ( "," TaskArg )* ")"

TaskArg :=
    "instances" "=" IntLit
  | "frame" "=" SizeLit
  | "wait_nodes" "=" IntLit
  | "prio" "=" IntLit
  | "reserve" "=" ReserveExpr
  | "group" "=" Ident

ReserveExpr :=
    "{" ReserveItem ( "," ReserveItem )* "}"

ReserveItem :=
    ResPath ":" IntLit                                    # flat leaf
  | Ident ":" "{" ReserveSubItem ( "," ReserveSubItem )* "}"  # bundle

ReserveSubItem :=
    Ident ( "." Ident )* ":" IntLit
```

### 3.2 Example

```simple
@task(instances=2, frame=224B, wait_nodes=1,
      reserve={NetRes:{pkt_pool:1, rxq.entries:1, rxq.waiters:1}})
async fn uart_rx() -> Never:
    val h = NetRes.pkt_pool.take()   # compile-time guaranteed slot
    loop:
        await uart.read_into(h.data_mut())
        await NetRes.rxq.push(h)
```

### 3.3 Reserve semantics

- `reserve={R:k}` means **each instance** of this task pre-claims `k` units from leaf `R`.
- For bundle shorthand, the compiler expands to leaf paths before checking.
- In strict mode, `pool.take()` on a reserved resource **cannot fail** (the capacity is
  statically guaranteed). The compiler elides runtime capacity checks.
- In relaxed mode, `pool.take()` returns `Option<Handle<T>>` and the reservation is
  a hint for the capacity checker.

### 3.4 Reserve validation algorithm (compile-time)

For each limited leaf `R` with capacity `R.CAP`:

```
sum = 0
for each task T that reserves R:
    sum = sum + (T.instances * T.reserve[R])
if sum > R.CAP:
    emit error: "reservation overflow: {sum} > {R.CAP} for {R.path}"
```

This is exact when spawns are bounded to the init phase (strict mode).

---

## 4) Task groups (shared instance caps)

### 4.1 Problem

Per-task `instances=N` limits each function separately. But sometimes you want:
"At most 4 network-worker tasks total, regardless of which worker function."

### 4.2 Grammar

```
TaskGroupDecl :=
    "task_group" Ident ":" Newline Indent GroupItem+ Dedent

GroupItem :=
    "cap" ":" IntLit
  | "frame" ":" SizeLit
  | "wait_nodes" ":" IntLit
```

### 4.3 Example

```simple
task_group NetWorkers:
    cap: 4
    frame: 256B
    wait_nodes: 1

@task(group=NetWorkers, frame=224B, wait_nodes=1,
      reserve={NetRes:{pkt_pool:1, rxq.entries:1, rxq.waiters:1}})
async fn dhcp_worker() -> Never:
    pass_todo

@task(group=NetWorkers, frame=240B, wait_nodes=1,
      reserve={NetRes:{stats:4}})
async fn http_worker() -> Never:
    pass_todo
```

### 4.4 Compile-time checks for groups

1. **Frame fit**: For each member task `T` in group `G`:
   `frame_size(T) <= G.frame`
   Error: "task 'http_worker' frame 240B exceeds group 'NetWorkers' frame 256B" (ok in this case)

2. **Wait nodes fit**: `T.wait_nodes <= G.wait_nodes`

3. **Spawn cap**: Total spawned group instances across all member tasks `<= G.cap`.
   This is checked at the init-phase spawn counting step.

4. **Reserve aggregation**: When computing reservation sums, group member tasks use
   `G.cap` as the max total instances (not per-task instances).

### 4.5 Memory cost

Group pool memory = `G.cap * G.frame`.

The slot size is `G.frame` (the max across all members). Tasks smaller than `G.frame`
waste `G.frame - frame_size(T)` bytes per slot. This is the standard fixed-block pool
tradeoff: zero fragmentation, bounded internal waste.

If waste is unacceptable, you can split tasks into separate groups by size class.

---

## 5) Compile-time verification (strict mode)

### 5.1 Profile configuration

```simple
profile baremetal:
    alloc: off
    gc: off
    async: on
    resource_check: strict

    max_tasks: 16
    readyq_cap: 64
    frame_max: 256B
    large_capture_max: 64B
    no_recursion_across_await: on
```

### 5.2 Verification passes (in compiler pipeline order)

The compiler runs these passes after async desugaring and before code generation.

#### Pass A: Async frame sizing (CFG liveness analysis)

**Goal**: Compute the exact size of each `async fn` state machine.

**Algorithm** (adapted from rustc's coroutine transform):

```
Input: MIR of async function with N suspend points (await expressions)

Step 1 — Storage liveness (forward dataflow):
    For each basic block B and local variable V:
        V is storage-live at B if there exists a path from
        a StorageLive(V) to B without passing through StorageDead(V).

Step 2 — Value liveness (backward dataflow):
    For each variable V and suspend point S:
        V is value-live across S if V is written before S
        AND may be read after S (without intervening write).

Step 3 — Intersection:
    saved_at[S] = { V | storage_live(V, S) AND value_live(V, S) }

Step 4 — Frame size computation:
    For each suspend point S:
        state_size[S] = sum(size_of(V) for V in saved_at[S]) + align_padding
    frame_size = max(state_size[S] for S in 0..N) + sizeof(FrameHeader)

Step 5 — Storage conflict analysis (overlap optimization):
    Build N x N conflict matrix:
        conflict[V1][V2] = exists S: V1 in saved_at[S] AND V2 in saved_at[S]
    Non-conflicting variables can share memory (graph coloring).
    frame_size_optimized = frame_size - overlap_savings
```

**Enforcement**:
- `frame_size_optimized(T) > T.frame` => error: "async fn '{T.name}' frame {actual}B exceeds declared {T.frame}"
- `frame_size_optimized(T) > profile.frame_max` => error: "frame exceeds profile limit {profile.frame_max}"

**Large capture detection**:
- For each variable V in `saved_at[S]`:
  if `size_of(V) > profile.large_capture_max`:
  warning: "large value '{V.name}' ({size}B) held across await in '{fn_name}' — consider boxing or splitting"
- This is a warning, not an error, because the frame might still fit.

#### Pass B: Spawn boundedness

**Goal**: Prove all task spawns occur in the init phase and count them exactly.

**Algorithm**:

```
Step 1 — Identify init functions:
    init_fns = { fn F | F has @entry or @boot attribute }

Step 2 — Build call graph from init:
    init_reachable = transitive_closure(init_fns, calls_graph)

Step 3 — Find spawn sites:
    for each call site C in the entire program:
        if C is a spawn(T) call:
            if C.containing_fn in init_reachable:
                # Check: spawn is before first await in the containing fn
                if C is after an await point in CFG:
                    error: "spawn of '{T}' after await in init function '{fn}'"
                else:
                    boot_spawns[T] += 1
            else:
                error: "spawn of '{T}' outside init phase (in '{C.containing_fn}')"

Step 4 — Check against limits:
    for each task T:
        if T has group G:
            # checked in group pass
            pass_dn
        else:
            if boot_spawns[T] > T.instances:
                error: "spawned {boot_spawns[T]} instances of '{T}', limit is {T.instances}"

Step 5 — Check group caps:
    for each group G:
        group_total = sum(boot_spawns[T] for T in G.members)
        if group_total > G.cap:
            error: "group '{G.name}' spawned {group_total} instances, cap is {G.cap}"
```

#### Pass C: Resource reservation sum

**Goal**: Prove reservations never exceed resource capacity.

**Algorithm**:

```
Step 1 — Flatten all reserves to leaf paths:
    for each task T:
        for each reserve item in T.reserve:
            if item is bundle shorthand:
                expand to leaf paths using resource struct definition
            leaf_reserves[T] = { (leaf_path, count) }

Step 2 — Compute totals per leaf:
    for each limited leaf R:
        total = 0
        for each task T that reserves R:
            if T has group G:
                # worst case: all G.cap instances are this task
                # BUT if multiple tasks in same group reserve same R,
                # the sum is bounded by the group members' reserves
                # weighted by their max possible instances.
                #
                # Conservative bound:
                total += T.reserve[R] * effective_instances(T)
            else:
                total += T.reserve[R] * T.instances

        if total > R.cap:
            error: "reservation overflow for '{R.path}': {total} > {R.cap}"

Step 3 — effective_instances for grouped tasks:
    For task T in group G:
        if all member tasks reserve the same leaf R:
            # tight bound: group cap * max per-instance reserve
            effective_instances(T) = boot_spawns[T]
        else:
            # conservative: assume all slots used by this task
            effective_instances(T) = min(boot_spawns[T], G.cap)
```

**Note on group reservation tightness**: When boot spawns are exact (strict mode),
`effective_instances(T) = boot_spawns[T]` gives an exact bound. The conservative
fallback only applies if spawn counting is imprecise.

#### Pass D: Waiter budget verification

**Goal**: Prove waiter slots are sufficient.

```
for each queue/event resource R with waiters=W:
    waiter_demand = 0
    for each task T that reserves R.waiters:
        waiter_demand += T.reserve[R.waiters] * effective_instances(T)
    if waiter_demand > W:
        error: "waiter overflow for '{R.path}': {waiter_demand} > {W}"

    # Also check: tasks that AWAIT on R but don't reserve waiters
    for each task T that contains `await R.pop()` or `await R.wait()`:
        if R.waiters not in T.reserve:
            error: "task '{T.name}' awaits on '{R.path}' but does not reserve waiters"
```

#### Pass E: Ready queue capacity

```
total_tasks = sum(effective_instances(T) for all tasks T)
if total_tasks > profile.readyq_cap:
    error: "total tasks {total_tasks} exceeds ready queue capacity {profile.readyq_cap}"
if total_tasks > profile.max_tasks:
    error: "total tasks {total_tasks} exceeds max_tasks {profile.max_tasks}"
```

#### Pass F: No recursion across await

When `profile.no_recursion_across_await: on`:

```
Build call graph G from all async functions.
For each cycle in G that passes through an await point:
    error: "recursive async call cycle detected: {cycle_path}"
    note: "recursion across await points creates unbounded frame growth"
```

### 5.3 Relaxed mode differences

In `resource_check: relaxed`:
- Pass B allows `spawn()` after `await` (uses runtime pool allocation)
- Pass C emits warnings instead of errors
- Pass D emits warnings instead of errors
- `pool.take()` returns `Option<Handle<T>>` instead of guaranteed `Handle<T>`
- Frames are still allocated from a fixed pool, but the pool can be a general
  fixed-block allocator instead of per-task static arrays

---

## 6) Runtime verification (debug builds)

Even with strict compile-time proofs, runtime instrumentation catches bugs
in the compiler itself and aids development.

### 6.1 Pool handle safety: index + generation

```simple
class Handle<T>:
    index: u16        # slot position in pool array
    generation: u16   # monotonic counter per slot

class PoolSlot<T>:
    generation: u16
    occupied: bool
    # union: when free, stores next_free index
    # union: when occupied, stores T data
    next_free: u16
    data: T?
```

**Allocation**:
```simple
me take() -> Handle<T>:
    val idx = self.free_head
    # debug assert: idx != SENTINEL
    val slot = self.slots[idx]
    self.free_head = slot.next_free
    slot.occupied = true
    # data initialized by caller
    Handle(index: idx, generation: slot.generation)
```

**Deallocation**:
```simple
me release(h: Handle<T>):
    val slot = self.slots[h.index]
    # debug assert: slot.generation == h.generation ("use-after-free")
    # debug assert: slot.occupied ("double-free")
    slot.occupied = false
    slot.generation = slot.generation + 1   # invalidates all stale handles
    slot.next_free = self.free_head
    self.free_head = h.index
```

**Access**:
```simple
fn get(h: Handle<T>) -> T:
    val slot = self.slots[h.index]
    # debug assert: slot.generation == h.generation
    # debug assert: slot.occupied
    slot.data ?? panic("invalid handle")
```

### 6.2 Watermark tracking

```simple
class ResourceWatermark:
    current: i64
    high_water: i64
    cap: i64

    me acquire():
        self.current = self.current + 1
        if self.current > self.high_water:
            self.high_water = self.current
        # debug assert: self.current <= self.cap

    me release_one():
        # debug assert: self.current > 0
        self.current = self.current - 1

    fn utilization() -> f64:
        if self.cap == 0:
            return 0.0
        self.high_water * 100 / self.cap
```

In debug builds, every `pool.take()`, `queue.push()`, `set.insert()`, `dict.insert()`
increments the watermark. On program exit (or on demand), print:

```
[resource] PktPool:     high=6/8   (75.0%)
[resource] RxQueue:     high=3/8   (37.5%)
[resource] StatsTable:  high=12/64 (18.8%)
```

This helps tune capacities.

### 6.3 Deadlock detection hint

```simple
fn scheduler_check_stuck():
    # Called when scheduler finds no ready tasks
    if ready_queue.is_empty() and waiter_count > 0:
        # All tasks are waiting but nothing can wake them
        print "[deadlock?] no ready tasks, {waiter_count} waiters pending"
        print "[deadlock?] check: are interrupts enabled? is a producer stuck?"
        # In debug: dump each waiter's task name and what it's waiting on
```

### 6.4 What to compile out in release

| Check | Debug | Release |
|-------|-------|---------|
| Handle generation validation | On | Off (strict proves safety) |
| Pool overflow assert | On | Off (strict proves no overflow) |
| Watermark tracking | On | Off |
| Deadlock hint | On | Off |
| Queue bounds check | On | Off (strict proves bounds) |

---

## 7) GC/managed profile

### 7.1 Defaults

```simple
profile managed:
    gc: on
    alloc: on
    async: on

    # These are IGNORED by default:
    frame_max: unlimited
    large_capture_max: unlimited
    resource_check: relaxed
    task_instances: unlimited
```

**Semantics**:
- If a resource is not `Limited` (no capacity declared), it is unbounded (heap-backed).
- `@task(instances=...)` defaults to `unlimited` unless a limit policy overrides it.
- Frame-size checks are disabled.
- `pool.take()` always returns `Handle<T>` (heap-allocates if needed).

### 7.2 Optional limit policies by scope

Even in GC mode, you may want limits for production safety (OOM prevention,
load shedding, testing).

**Scope hierarchy** (nearest wins):

```
app/lib init  <  file  <  class  <  fn  <  @limit attribute
```

**SDN config syntax** (in `simple.build.sdn` or `__init__.spl`):

```simple
# Library-level policy (in __init__.spl)
limits:
    tasks.max_instances: 1000
    tasks.frame_max: 4KB        # enable frame checks even in GC mode
    resources.require_limited: false

# File-level policy (at top of file)
@limits(tasks.max_instances=200)

# Per-task override
@limit(max_instances=8)
@task
async fn parser_worker():
    pass_todo
```

**Resolution**: `@limit` on the task > file `@limits` > module `limits:` block > profile default.

### 7.3 Limit policy fields

| Field | Type | Default (managed) | Meaning |
|-------|------|--------------------|---------|
| `tasks.max_instances` | i64 | unlimited | Max concurrent task instances |
| `tasks.frame_max` | size | unlimited | Max async frame size |
| `resources.require_limited` | bool | false | Error if resource has no capacity |
| `resources.max_entries` | i64 | unlimited | Default cap for unbounded collections |

### 7.4 Behavior difference summary

| Feature | Baremetal strict | Baremetal relaxed | Managed |
|---------|-----------------|-------------------|---------|
| Frame sizing | Compile error if exceeds | Warning | Ignored (unless policy) |
| Spawn counting | Exact, init-only | Approximate | Not checked (unless policy) |
| Reserve check | Compile error | Warning | Not checked |
| pool.take() | Always succeeds | Returns Option | Always succeeds (heap fallback) |
| Waiter check | Compile error | Warning | Not checked |
| Handle safety | Generation (debug) | Generation | GC handles use-after-free |
| Watermarks | Debug builds | Debug builds | Optional |

---

## 8) Minimum feature set (MVP)

### 8.1 Phase 1: Core async (build on existing `async_core.spl` + `desugar_async.spl`)

1. **Stackless async lowering to state machine** — extend `desugar_async.spl`
   - Already has `analyze_suspensions()`, `generate_state_enum()`, `generate_poll_function()`
   - Add: MIR-level liveness analysis for frame sizing
   - Add: storage conflict matrix for overlap optimization

2. **Frame sizing + `frame_max` enforcement** — new compiler pass
   - Compute frame size per async fn
   - Enforce `profile.frame_max`
   - "Large capture across await" warning

3. **`@task(...)` async fn + static instance pools** — new
   - Parse `@task` attribute
   - Generate static `TaskPool<F, N>` for each task
   - Embed frame data in pool slots

4. **Bounded awaitables** — extend `async_embedded.spl`
   - `Event<N>` (N waiters)
   - `Timer.after_ms()` (uses hardware timer interrupt)
   - Waiter node accounting

### 8.2 Phase 2: Resources

5. **`resource pool` + `resource queue`** — new declarations
   - Fixed-capacity pool with generational handles
   - Fixed-capacity queue with waiter list

6. **Reserve accounting** (strict mode) — new compiler pass
   - Parse `reserve={}` in `@task`
   - Reservation sum check (Pass C)
   - Spawn counting (Pass B)

### 8.3 Phase 3: Extensions

7. **`resource dict` / `resource set`** — new declarations

8. **`resource struct` bundles + reserve path expansion** — new
   - Composite resources
   - Leaf flattening

9. **`task_group`** — shared instance caps

### 8.4 What ships with each phase

| Phase | What works | What's proven |
|-------|-----------|---------------|
| 1 | async/await on baremetal, fixed pools | Frame fits, no heap |
| 1+2 | Resource pools, queues, reservations | No resource exhaustion |
| 1+2+3 | Groups, bundles, dicts/sets | Full capacity discipline |

---

## 9) Async frame header layout (runtime ABI)

### 9.1 Frame header (24 bytes)

```
Offset  Size  Field            Description
0x00    4     state            Atomic u32: lifecycle bits
0x04    4     run_queue_next   Index into task array (SENTINEL = 0xFFFF)
0x08    4     poll_fn_idx      Index into vtable (type-erased poll dispatch)
0x0C    4     timer_expires    Tick count for timer wake-up (0 = no timer)
0x10    2     generation       Generation counter for handle safety
0x12    1     priority         Priority level (0=Critical..4=Idle)
0x13    1     flags            Bit flags (see below)
0x14    4     waiter_head      Index of first WaiterNode (SENTINEL = 0xFFFF)
0x18    ...   future_data      The actual state machine bytes (variable size)
```

**State bits** (u32):

```
Bit 0:  SPAWNED       (0x01)  — task slot is occupied
Bit 1:  ENQUEUED      (0x02)  — in the ready queue
Bit 2:  NOTIFIED      (0x04)  — woken by interrupt or another task
Bit 3:  COMPLETED     (0x08)  — poll returned Ready
Bit 4:  CANCELLED     (0x10)  — marked for cancellation
```

**Flags byte**:

```
Bit 0:  IN_GROUP      — task belongs to a task_group
Bit 1:  HAS_WAITER    — task is currently waiting on a resource
Bit 2:  RESERVED      — task has pre-claimed resource tokens
```

### 9.2 Waiter node layout (8 bytes, embedded in frame)

```
Offset  Size  Field         Description
0x00    2     next          Index of next waiter (SENTINEL = 0xFFFF)
0x02    2     prev          Index of previous waiter (for O(1) removal)
0x04    2     task_idx      Index of the owning task (for wake dispatch)
0x06    2     _pad          Alignment padding
```

The waiter node lives **inside the task's own frame** (in the `future_data` region),
not in a separately allocated structure. When a task awaits a resource:

1. It creates a `WaiterNode` in its state machine's current variant.
2. It inserts the node into the resource's doubly-linked waiter list.
3. When the resource becomes available, it walks the list and sets `NOTIFIED`
   on each waiter's task.
4. The scheduler dequeues notified tasks.

The waiter list is FIFO for fairness (longest-waiting task wakes first).

### 9.3 Pool slot layout

```
Offset  Size           Field
0x00    2              generation (u16)
0x02    1              flags (occupied: bit 0)
0x03    1              _pad
0x04    sizeof(T)      data (or next_free: u16 when !occupied)
```

Total slot size = `4 + align_up(sizeof(T), 4)`.

### 9.4 Ready queue layout

Fixed-capacity circular buffer of task indices:

```simple
class ReadyQueue:
    buf: [u16]       # pre-allocated to readyq_cap
    head: u16
    tail: u16
    count: u16
    cap: u16
```

Operations are O(1). Priority is handled by maintaining separate queues
per priority level (5 queues for Critical..Idle), or by a single sorted
insertion (acceptable for small task counts).

---

## 10) Static analysis algorithm detail

### 10.1 CFG construction for async functions

After async desugaring produces a state enum + poll function:

```
FetchState:
    State0(url: text)
    State1(url: text, future: Future<Response>)
    State2(response: Response, future: Future<text>)
```

The poll function's match arms form a CFG:

```
BB0 (entry):  switchInt(state_discriminant) -> [0: BB1, 1: BB2, 2: BB3]

BB1 (State0):
    http_get(url) -> future
    state = State1(url, future)
    return (state, Pending)         # suspend point 0

BB2 (State1):
    poll(future) -> match
        Ready(response) -> BB4
        Pending -> return (state, Pending)   # re-suspend

BB4:
    response.text() -> future2
    state = State2(response, future2)
    return (state, Pending)         # suspend point 1

BB3 (State2):
    poll(future2) -> match
        Ready(text) -> BB5
        Pending -> return (state, Pending)   # re-suspend

BB5 (terminal):
    return (Completed, Ready(text))
```

### 10.2 Liveness dataflow equations

**Storage liveness** (forward, bit-per-variable):

```
SL_in[BB]  = union(SL_out[pred] for pred in predecessors(BB))
SL_out[BB] = (SL_in[BB] - kill_storage[BB]) | gen_storage[BB]

gen_storage[BB]  = { V | StorageLive(V) in BB }
kill_storage[BB] = { V | StorageDead(V) in BB }
```

**Value liveness** (backward, bit-per-variable):

```
VL_out[BB] = union(VL_in[succ] for succ in successors(BB))
VL_in[BB]  = (VL_out[BB] - def[BB]) | use[BB]

use[BB]  = { V | V is read in BB before any write to V }
def[BB]  = { V | V is written in BB }
```

**Live across suspend point S** (in basic block BB_S):

```
saved_at[S] = SL_out[BB_S] & VL_out[BB_S]
```

### 10.3 Overlap optimization (storage conflict graph)

```
For each pair of saved variables (V1, V2):
    conflict(V1, V2) = exists S in suspend_points:
        V1 in saved_at[S] AND V2 in saved_at[S]

Build conflict graph G where:
    nodes = all saved variables
    edges = conflict pairs

Perform graph coloring on G:
    Each color class can share the same memory offset.
    frame_savings = sum(size_of(V)) - sum(size_of(color_class_max))
```

For most embedded async functions (2-5 suspend points, <20 locals), the conflict
graph is small enough for optimal coloring.

### 10.4 Spawn counting with call graph reachability

```
Input: Module AST after desugaring

Step 1: Build call graph
    nodes = all functions
    edges = (caller, callee) for each call site
    annotate edges with: is_spawn, is_after_await

Step 2: Classify functions
    init_set = { F | has_attr(@entry) or has_attr(@boot) }
    task_set = { F | has_attr(@task) }

Step 3: Forward reachability from init
    init_reachable = BFS(init_set, call_graph)

Step 4: Count spawns
    for each spawn(T) call site C:
        if C.caller not in init_reachable:
            ERROR("spawn outside init phase")
        if C.is_after_await:
            ERROR("spawn after await in init")
        spawn_count[T] += 1

Step 5: Verify
    for each task T not in any group:
        assert spawn_count[T] <= T.instances
    for each group G:
        group_sum = sum(spawn_count[T] for T in G.members)
        assert group_sum <= G.cap
```

### 10.5 Reservation sum with group-aware bounds

```
Input: spawn_count from Pass B, reserve declarations from @task

For each limited leaf R with capacity C:
    demand = 0
    for each task T that has reserve[R] = k:
        if T in group G:
            instances = spawn_count[T]   # exact from Pass B
        else:
            instances = spawn_count[T]   # exact from Pass B
        demand += k * instances

    if demand > C:
        ERROR with details:
            "Resource '{R.path}' overcommitted: {demand} > {C}"
            for each contributing task:
                "  {T.name}: {k} * {instances} = {k * instances}"
```

---

## 11) End-to-end example

```simple
profile baremetal:
    alloc: off
    gc: off
    async: on
    resource_check: strict
    max_tasks: 16
    readyq_cap: 64
    frame_max: 256B
    large_capture_max: 64B
    no_recursion_across_await: on

class Packet:
    len: u16
    data: [u8]    # fixed-size via resource declaration context

class Stats:
    rx: u32
    tx: u32

# Resources
resource struct NetRes:
    pkt_pool: Packet[8]
    rxq: Queue<Handle<PktPool>, 8, waiters=2>
    stats: Dict<u16, Stats, 64>

# Shared task group
task_group NetWorkers:
    cap: 4
    frame: 256B
    wait_nodes: 1

# Producer task
@task(group=NetWorkers, frame=224B, wait_nodes=1,
      reserve={NetRes:{pkt_pool:1, rxq.entries:1, rxq.waiters:1}})
async fn uart_rx() -> Never:
    val h = NetRes.pkt_pool.take()
    loop:
        await uart.read_into(h.data_mut())
        await NetRes.rxq.push(h)

# Consumer task
@task(group=NetWorkers, frame=240B, wait_nodes=1,
      reserve={NetRes:{stats:4}})
async fn parser() -> Never:
    loop:
        val h = await NetRes.rxq.pop()
        val conn_id = parse_conn(h)
        NetRes.stats.insert_or_update(conn_id, fn(s): Stats(rx: s.rx + 1, tx: s.tx))
        NetRes.pkt_pool.release(h)

# Entry point
@entry
async fn main() -> Never:
    spawn uart_rx()
    spawn parser()
    await Scheduler.idle_forever()
```

### What the compiler proves (strict mode):

| Check | Computation | Result |
|-------|------------|--------|
| Group frame fit | max(224, 240) <= 256 | OK |
| Group spawn cap | 1 + 1 = 2 <= 4 | OK |
| `NetRes.pkt_pool` (Slots=8) | 1*1 + 0*1 = 1 <= 8 | OK |
| `NetRes.rxq.entries` (Entries=8) | 1*1 + 0*1 = 1 <= 8 | OK |
| `NetRes.rxq.waiters` (Waiters=2) | 1*1 + 0*1 = 1 <= 2 | OK |
| `NetRes.stats` (Entries=64) | 0*1 + 4*1 = 4 <= 64 | OK |
| Total tasks | 2 <= 16 | OK |
| Ready queue | 2 <= 64 | OK |
| uart_rx frame | computed <= 224B | checked |
| parser frame | computed <= 240B | checked |
| No spawn after await | main spawns before idle_forever | OK |

---

## 12) Robustness improvements summary

| v0.2 gap | v0.3 addition |
|----------|---------------|
| No formal trait for bounded resources | `Limited` + `LimitedComposite` traits |
| Flat reserves only | Bundle path expansion (`NetRes:{pkt_pool:1, rxq.entries:2}`) |
| Per-task instance limits only | `task_group` shared caps |
| Vague "compile-time check" | 6 concrete passes (A-F) with algorithms |
| No runtime safety net | Generational handles, watermarks, deadlock hint |
| No GC mode story | Managed profile with optional hierarchical limits |
| Waiter accounting hand-waved | Waiters as first-class limited leaf + Pass D |
| No frame overlap optimization | Storage conflict analysis + graph coloring |
| No recursion detection | Pass F: cycle detection across await points |
| Unclear reserved vs regular take | `take()` infallible in strict, `Option` in relaxed |

---

## Appendix A: Relationship to existing codebase

| Existing code | Role in v0.3 |
|---------------|--------------|
| `src/std/async_core.spl` | Base types (Poll, TaskState, Priority) — reused |
| `src/std/async_embedded.spl` | EmbeddedScheduler — extended with frame pools |
| `src/compiler/desugar_async.spl` | State machine generation — extended with liveness |
| `src/compiler/hir_lowering/async.spl` | Async validation — extended with reservation checks |
| `src/std/baremetal/allocator.spl` | FixedBlockAllocator — basis for task pool |
| `src/std/baremetal/interrupt.spl` | Interrupt handlers — integrate with async wakers |
| `src/std/baremetal/syscall.spl` | Timer syscalls — basis for Timer.after_ms() |

## Appendix B: References

- [rustc coroutine transform](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/)
- [Tyler Mandry — How Rust Optimizes Async/Await](https://tmandry.gitlab.io/blog/posts/optimizing-await-1/)
- [Embassy TaskStorage/TaskPool](https://docs.embassy.dev/embassy-executor/git/cortex-m/raw/struct.TaskStorage.html)
- [RTIC Stack Resource Policy](https://rtic.rs/2/book/en/by-example/resources.html)
- [lilos intrusive waiter list](https://docs.rs/lilos/latest/lilos/list/index.html)
- [RFC 3014 — must_not_suspend lint](https://rust-lang.github.io/rfcs/3014-must-not-suspend-lint.html)
- [generational-arena](https://github.com/fitzgen/generational-arena)
