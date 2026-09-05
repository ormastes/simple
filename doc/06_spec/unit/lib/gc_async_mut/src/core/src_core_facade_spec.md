# src_core_facade_spec

> Purpose and audience: facade smoke verification for the gc_async_mut src core

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# src_core_facade_spec

Purpose and audience: facade smoke verification for the gc_async_mut src core

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/src/core/src_core_facade_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: facade smoke verification for the gc_async_mut src core
modules. Scope: context managers, decorators, seeded random, regex helpers,
and synchronization primitives reachable through the facade re-exports.
Audience: stdlib core maintainers.

research: doc/01_research/lib/collections_impl/collections.md ; plan: doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16_tldr.md ; architecture: doc/04_architecture/lib/runtime_family_stdlib_surface.md ; design: doc/05_design/lib/stdlib/aop_support_matrix.md
requirements: doc/02_requirements/language/collections/hashmap_basic.md

## Scenarios

### gc_async_mut src core facade

#### re-exports context, decorator, random, and regex helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Context, decorator, random, and regex helpers (expected show, folded, detail, or skip)


- Exercise timer, lock, and transaction context managers
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: timer.name equals `facade`
   - Expected: lock.is_unlocked() is true
   - Expected: tx.state equals `TransactionState.Pending`
- Exercise decorator record constructors and accessors
   - Expected: cached_fn.cache_info()["hits"] equals `0`
   - Expected: logged_fn.call_count equals `0`
   - Expected: deprecated_fn.warned is false
   - Expected: timeout_result.is_success() is true
   - Expected: timeout_fn.timeout_seconds equals `10`
- Exercise seeded random state round-trip and bounded draws
- Exercise regex compile, search, escape, and class builders
   - Expected: pattern.get_pattern() equals `ab`
   - Expected: compile("ab").get_pattern() equals `ab`
   - Expected: search("bc", "abc").get() equals `bc`
   - Expected: escape("a.b") equals `a\\.b`
   - Expected: one_or_more(digit()) equals `[0-9]+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-CORE-FACADE
step("Exercise timer, lock, and transaction context managers")
val t0 = time_now()
val timer = TimerContext.create("facade")
expect(timer.name).to_equal("facade")
expect(time_now()).to_be_greater_than(t0)
val lock = Lock.create()
expect(lock.is_unlocked()).to_equal(true)
val tx = TransactionContext.create()
expect(tx.state).to_equal(TransactionState.Pending)

step("Exercise decorator record constructors and accessors")
val cached_fn = CachedFunction(wrapped_fn: nil, cache: {}, hits: 0, misses: 0)

expect(cached_fn.cache_info()["hits"]).to_equal(0)  # oracle: 0 = freshly constructed cache has recorded no hits
val logged_fn = LoggedFunction(wrapped_fn: nil, name: "noop", call_count: 0)
# oracle: 0 = the logged wrapper starts with a zero call count.
expect(logged_fn.call_count).to_equal(0)  # oracle: 0 = logged wrapper starts with a zero call count
val deprecated_fn = DeprecatedFunction(wrapped_fn: nil, message: "old", warned: false)
expect(deprecated_fn.warned).to_equal(false)
val timeout_result = TimeoutResult(value: nil, success: true)
expect(timeout_result.is_success()).to_equal(true)
val timeout_fn = TimeoutFunction(wrapped_fn: nil, timeout_seconds: 10)
# oracle: 10 = the configured timeout_seconds echoed back by the accessor.
expect(timeout_fn.timeout_seconds).to_equal(10)  # oracle: 10 = configured timeout echoed back by the accessor

step("Exercise seeded random state round-trip and bounded draws")
seed(42)
val state = getstate()
setstate(state)
expect(randrange(0, 10, 1)).to_be_less_than(10)
expect(uniform(0.0, 1.0)).to_be_less_than(1.0)

step("Exercise regex compile, search, escape, and class builders")
val pattern = Pattern(pattern: "ab")
expect(pattern.get_pattern()).to_equal("ab")
expect(compile("ab").get_pattern()).to_equal("ab")
expect(search("bc", "abc").get()).to_equal("bc")
expect(escape("a.b")).to_equal("a\\.b")
expect(one_or_more(digit())).to_equal("[0-9]+")
```

</details>

#### re-exports synchronization primitives

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Synchronization primitives (expected show, folded, detail, or skip)


- Exercise Atomic create, fetch_add, and load
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: atomic.load() equals `1`
   - Expected: atomic.fetch_add(2) equals `1`
   - Expected: atomic.load() equals `3`
- Exercise Mutex try_lock, is_locked, and unlock
   - Expected: mutex.try_lock() is true
   - Expected: mutex.is_locked() is true
   - Expected: mutex.is_locked() is false
- Exercise RwLock read, write, and into_inner
   - Expected: rw.read() equals `read`
   - Expected: rw.into_inner() equals `write`
- Exercise Semaphore acquire and permit accounting
   - Expected: sem.try_acquire(1) is true
   - Expected: sem.available_permits() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-CORE-FACADE
step("Exercise Atomic create, fetch_add, and load")
var atomic = Atomic.create(1)

expect(atomic.load()).to_equal(1)  # oracle: 1 = initial value passed to Atomic.create

expect(atomic.fetch_add(2)).to_equal(1)  # oracle: 1 = fetch_add returns the pre-increment value

expect(atomic.load()).to_equal(3)  # oracle: 3 = stored value after adding 2 to initial 1

step("Exercise Mutex try_lock, is_locked, and unlock")
var mutex = Mutex.create("data")
expect(mutex.try_lock()).to_equal(true)
expect(mutex.is_locked()).to_equal(true)
mutex.unlock()
expect(mutex.is_locked()).to_equal(false)

step("Exercise RwLock read, write, and into_inner")
var rw = RwLock.create("read")
expect(rw.read()).to_equal("read")
rw.read_unlock()
rw.write("write")
expect(rw.into_inner()).to_equal("write")

step("Exercise Semaphore acquire and permit accounting")
var sem = Semaphore.create(2)
expect(sem.try_acquire(1)).to_equal(true)

expect(sem.available_permits()).to_equal(1)  # oracle: 1 = 2 initial permits minus 1 acquired
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-CORE-FACADE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8860670425aa785accd468806d7d312be02122c95d0f7c6edea9239c22654681`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8860670425aa785accd468806d7d312be02122c95d0f7c6edea9239c22654681`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8860670425aa785accd468806d7d312be02122c95d0f7c6edea9239c22654681`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: unit/lib/gc_async_mut/src/core/src_core_facade_spec.spl
mirror: src/core/src_core_facade_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
src/core/src_core_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
src/core/src_core_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
