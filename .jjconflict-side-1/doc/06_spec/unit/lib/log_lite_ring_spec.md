# log_lite_ring_spec

log-lib-drivers Phase 4 spec — SPSC lite ring (no-alloc, ISR/panic-safe).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/log_lite_ring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — SPSC lite ring (no-alloc, ISR/panic-safe).

Covers AC-5 (lite logger: no alloc, no blocking lock, ISR/panic-safe)
and AC-6c (lite-log ISR-safe emission, no alloc, bounded time).

EXPECTED RED PHASE: this file will FAIL TO COMPILE until Phase 5 lands
the K-1 atomic externs (rt_atomic_fetch_add_u64, rt_atomic_load_u64,
rt_atomic_store_u64, rt_atomic_store_u8) and the ring/facade modules.
That is the design — see state.md §K Open Risk K-1.

Phase 3 contract (locked, §C):
  Record layout: total = 40 bytes, naturally 8-byte aligned, no padding.
    seq:        u64 @  0   (monotonic, set by producer atomic-add)
    ts_ns:      u64 @  8   (rt_time_now_ns at emission)
    p0:         u64 @ 16   (numeric payload 0)
    p1:         u64 @ 24   (numeric payload 1)
    fmt_handle: u32 @ 32   (index into static fmt-string table)
    subsys:     u16 @ 36
    level:      u8  @ 38
    flags:      u8  @ 39   (bit0 = panic_origin; bit1 = ratelimited)

  NOTE — task description's offset table (`level@16`) was wrong; the
  Phase-3 architecture-§C ordering above is the locked contract because
  it gives natural alignment with zero padding (cardinality verified:
  u64*4 + u32 + u16 + u8 + u8 = 40).

  Capacity: power-of-two, default 1024 records (40 KiB).
  Cap range: [64, 16384]. Mask = cap - 1.

  Producer protocol:
    - rt_atomic_fetch_add_u64(&next_seq, 1)
    - if previous slot's seq is in (seq_local - cap, seq_local) — full,
      atomic-add dropped, return false
    - otherwise write fields and release-store seq

  Drainer: log_drain(max) — non-IRQ poll, no locks.

## Scenarios

### log lite ring — record layout (AC-5)

#### AC-5: LogRecord is exactly 40 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(record_size_bytes()).to_equal(40)
```

</details>

#### AC-5: field offsets match Phase-3 §C lock

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase-3 ordering — task description offsets were wrong; this
# is the natural-alignment layout the engineer must implement.
expect(record_offset_seq()).to_equal(0)
expect(record_offset_ts_ns()).to_equal(8)
expect(record_offset_p0()).to_equal(16)
expect(record_offset_p1()).to_equal(24)
expect(record_offset_fmt_handle()).to_equal(32)
expect(record_offset_subsys()).to_equal(36)
expect(record_offset_level()).to_equal(38)
expect(record_offset_flags()).to_equal(39)
```

</details>

### log lite ring — capacity (AC-5)

#### AC-5: default capacity is 1024 (power of two)

1. log ring init
   - Expected: log_ring_capacity() equals `1024`
   - Expected: RING_CAP_DEFAULT equals `1024`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(RING_CAP_DEFAULT_LOG2)
expect(log_ring_capacity()).to_equal(1024)
expect(RING_CAP_DEFAULT).to_equal(1024)
```

</details>

#### AC-5: capacity is always a power of two (default mask = cap-1)

1. log ring init
   - Expected: cap & (cap - 1) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(RING_CAP_DEFAULT_LOG2)
val cap = log_ring_capacity()
# cap & (cap - 1) == 0 for any power-of-two
expect(cap & (cap - 1)).to_equal(0)
```

</details>

### log lite ring — producer/drainer ordering (AC-5, AC-6c)

#### AC-5: producer fills ring, drainer reads back in seq order

1. log ring init

2. log ring drain

3. log ring push
   - Expected: log_ring_pending() equals `5`
   - Expected: seen.len() equals `5`
   - Expected: seen[j].p0 equals `j`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(6)  # 64 records — small for the test
# Drain anything stale.
log_ring_drain(1024)
# Push 5 records with increasing p0.
var i = 0
while i < 5:
    log_ring_push(LOG_INFO, SUBSYS_KERN, 0, i, 0, 0)
    i = i + 1
expect(log_ring_pending()).to_equal(5)
# Drainer pulls them; observation order matches push order.
val seen = drain_to_list(5)
expect(seen.len()).to_equal(5)
var j = 0
while j < 5:
    expect(seen[j].p0).to_equal(j)
    j = j + 1
```

</details>

#### AC-5: head wraps around at capacity boundary

1. log ring init

2. log ring drain

3. log ring push
   - Expected: log_ring_dropped() equals `0`
   - Expected: log_ring_drain(1024) equals `64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(6)  # 64 records
log_ring_drain(1024)
# Push exactly cap records and drain — no drops.
var k = 0
while k < 64:
    log_ring_push(LOG_INFO, SUBSYS_KERN, 0, k, 0, 0)
    k = k + 1
expect(log_ring_dropped()).to_equal(0)
expect(log_ring_drain(1024)).to_equal(64)
```

</details>

### log lite ring — overflow drop semantics (AC-5, AC-6c)

#### AC-6c: pushing N+1 records when ring is full drops exactly 1

1. log ring init

2. log ring drain

3. log ring push

4. log ring push
   - Expected: log_ring_dropped() - baseline_drops equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(6)  # cap = 64
log_ring_drain(1024)
# Reset dropped counter is a Phase-5 concern; capture baseline.
val baseline_drops = log_ring_dropped()
# Fill to cap WITHOUT draining.
var i = 0
while i < 64:
    log_ring_push(LOG_INFO, SUBSYS_KERN, 0, i, 0, 0)
    i = i + 1
# 65th push must increment dropped counter by 1.
log_ring_push(LOG_INFO, SUBSYS_KERN, 0, 999, 0, 0)
expect(log_ring_dropped() - baseline_drops).to_equal(1)
```

</details>

### log lite ring — panic-mode flush (AC-5)

#### AC-5: log_panic_flush switches all backends to sync, drains ring

1. log ring init

2. ring backend clear

3. log ring push

4. log ring push

5. log panic flush
   - Expected: panic_mode_active() is true
   - Expected: log_ring_pending() equals `0`

6. log info
   - Expected: log_ring_pending() equals `0`

7. log remove backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(RING_CAP_DEFAULT_LOG2)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
# Buffered emissions before panic.
log_ring_push(LOG_INFO, SUBSYS_KERN, 0, 1, 0, 0)
log_ring_push(LOG_INFO, SUBSYS_KERN, 0, 2, 0, 0)
# Panic flush: must drain pending + flip sync mode.
log_panic_flush()
expect(panic_mode_active()).to_equal(true)
expect(log_ring_pending()).to_equal(0)
# Subsequent emissions go direct, not through the ring.
log_info(SUBSYS_KERN, "post-panic direct")
# Direct path bypasses ring; pending stays 0.
expect(log_ring_pending()).to_equal(0)
log_remove_backend(id)
```

</details>

### log lite ring — no-alloc contract (AC-5, AC-6c)

#### AC-6c: log_ring_push performs zero allocations (1000 calls)

1. log ring init

2. alloc probe reset

3. log ring push
   - Expected: alloc_probe_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_ring_init(RING_CAP_DEFAULT_LOG2)
# TODO(phase-5): replace stub with real g_alloc_probe once K-1 lands.
alloc_probe_reset()
var i = 0
while i < 1000:
    log_ring_push(LOG_INFO, SUBSYS_IRQ, 0, i, 0, 0)
    i = i + 1
expect(alloc_probe_count()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

