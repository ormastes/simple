# UTF-8 and internationalized text memory-counter availability

> This lane measures runtime-owned memory counters after constructing its

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UTF-8 and internationalized text memory-counter availability

This lane measures runtime-owned memory counters after constructing its

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/utf8_internationalized_text_architecture.md |
| Plan | doc/03_plan/perf/utf8_internationalized_text_architecture.md |
| Design | doc/05_design/lib/text_i18n/utf8_internationalized_text_architecture.md |
| Research | doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md |
| Source | `test/05_perf/text_i18n/utf8_internationalized_text_memory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

This lane measures runtime-owned memory counters after constructing its
corpora. Unlike RSS, these counters are local to the test process and are not
inflated by unrelated processes on a busy host. It records UTF-8 scan,
scalar-access, and UTF-16 conversion live-header, auxiliary-buffer, and array
capacity deltas. The deployed interpreter does not register allocation-count
or heap-peak externs, so those dimensions remain explicitly unavailable rather
than being synthesized.

It is intended for runtime, text, compiler, performance, and release owners.

## Overview

The lane snapshots three runtime-owned counters after input setup: live heap
header bytes, auxiliary backing-buffer bytes, and array backing-capacity bytes.
Each operation runs between snapshots. Growth uses nonnegative subtraction so
a reset cannot become a fictional negative allocation.

The operations are repeated UTF-8 validation/counting, repeated scalar access,
and one UTF-16-to-UTF-8 conversion. Checksums keep results observable.

## Syntax and examples

Run:

```text
bin/simple test test/05_perf/text_i18n/utf8_internationalized_text_memory_spec.spl --mode=interpreter --no-cache
```

Representative rows:

```text
text_memory operation=utf8_scan counter_status=unavailable ...
text_memory operation=ascii_scalar_access counter_status=unavailable ...
text_memory operation=utf16_to_utf8 counter_status=unavailable ...
```

`measured` requires at least one observable counter. `unavailable` means every
registered counter is zero and must never be rewritten as zero allocations.

## Corpus

The UTF-8 fixture is exactly 16,384 ASCII bytes cycling `A` through `Z`.
Construction occurs before snapshots. The scalar fixture is the fixed
36-scalar lowercase-and-digit ASCII string and executes 4,096 accesses.

The UTF-16 fixture contains 8,190 code units repeating ASCII `A`, precomposed
`é`, Korean `한`, and the surrogate pair for U+1F600. Its current conversion
produces 16,380 UTF-8 bytes.

## Metric definitions

- `live_growth_bytes`: nonnegative heap-header growth.
- `aux_growth_bytes`: nonnegative auxiliary-buffer growth.
- `array_capacity_growth_bytes`: nonnegative retained array capacity growth.
- `live_bytes`: post-operation current header bytes.
- `allocation_count=unavailable`: missing interpreter capability.
- `heap_peak_bytes=unavailable`: missing interpreter capability.
- `checksum`: observable work/result witness.

These counters exclude native allocators, mapped catalogs, font-library state,
GPU allocations, driver memory, and operating-system pages.

## Pass and fail interpretation

On an observable backend, UTF-8 scanning retains zero growth after setup.
Scalar access has a one-MiB smoke ceiling per dimension. UTF-16 conversion has
a combined 64-MiB ceiling while its intermediate-array defect remains open.

On an unobservable backend, all registered counters must consistently remain
zero. This is a passing capability observation, not memory qualification.

## Reproducibility

1. Construct fixtures before snapshots.
2. Preserve corpus sizes and operation counts.
3. Record revision, runtime profile, execution mode, host, and architecture.
4. Never compare measured and unavailable rows.
5. Never infer allocation count from retained-byte growth.
6. Pair this lane with isolated RSS/HWM and `text-i18n-perf-v1` receipts.
7. Preserve unavailable dimensions verbatim.

## Rendering scope

Engine2D and Engine3D require separate isolated-process RSS comparisons plus
shaped-run bytes, atlas capacity/waste, dirty/upload/eviction bytes, GPU
resource high-water bytes, queue completion, and device-origin readback. CPU
fallback pixels are not device-memory evidence.

## No-allocation scope

No-allocation profiles require exact-zero receipts after initialization,
bounded fixed buffers, and deterministic capacity errors. An unavailable
counter backend cannot qualify those profiles.

## Known limitation and remediation

The deployed interpreter registers live, auxiliary, and array-capacity calls
but observes all three as zero here. It does not register heap peak or
allocation count. See
`doc/08_tracking/bug/interpreter_text_memory_counters_unobservable_2026-08-26.md`.

Resolution requires cross-profile registration, a deliberate-allocation
positive control, and native parity. Isolated RSS/HWM remains the portable
whole-process memory evidence until then.

## Release rule

An all-zero runtime snapshot is reported as unavailable, never interpreted as
proof of zero allocation. The ceilings are safety bounds when counters are
observable. Matched before/after receipts remain the release authority.

## Scenarios

### UTF-8 internationalized text memory performance

#### records allocation-free UTF-8 validation and counting after corpus setup

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = memory_ascii_bytes()
val before = memory_snapshot()
var checksum: i64 = 0
var i: i64 = 0
while i < 64:
    if utf8_is_valid(bytes): checksum = checksum + 1
    checksum = checksum + utf8_count_codepoints(bytes)
    i = i + 1
val after = memory_snapshot()
val live_growth = delta(after.live_bytes, before.live_bytes)
val aux_growth = delta(after.aux_live_bytes, before.aux_live_bytes)
val capacity_growth = delta(after.array_capacity_bytes, before.array_capacity_bytes)
expect(checksum).to_be_greater_than(0)
expect(live_growth).to_equal(0)
expect(aux_growth).to_equal(0)
expect(capacity_growth).to_equal(0)
val status = if counters_available(after): "measured" else: "unavailable"
print "text_memory operation=utf8_scan counter_status={status} iterations=64 input_bytes={bytes.len()} allocation_count=unavailable heap_peak_bytes=unavailable live_growth_bytes={live_growth} aux_growth_bytes={aux_growth} array_capacity_growth_bytes={capacity_growth} live_bytes={after.live_bytes} checksum={checksum}"
```

</details>

#### bounds scalar-access allocation growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "abcdefghijklmnopqrstuvwxyz0123456789"
val before = memory_snapshot()
var checksum: i64 = 0
var i: i64 = 0
while i < 4096:
    checksum = checksum + str_char_at(value, i % value.len()).char_code_at(0)
    i = i + 1
val after = memory_snapshot()
val live_growth = delta(after.live_bytes, before.live_bytes)
val aux_growth = delta(after.aux_live_bytes, before.aux_live_bytes)
val capacity_growth = delta(after.array_capacity_bytes, before.array_capacity_bytes)
expect(checksum).to_be_greater_than(0)
expect(live_growth).to_be_less_than(1048577)
expect(aux_growth).to_be_less_than(1048577)
expect(capacity_growth).to_be_less_than(1048577)
val status = if counters_available(after): "measured" else: "unavailable"
print "text_memory operation=ascii_scalar_access counter_status={status} iterations=4096 allocation_count=unavailable heap_peak_bytes=unavailable live_growth_bytes={live_growth} aux_growth_bytes={aux_growth} array_capacity_growth_bytes={capacity_growth} live_bytes={after.live_bytes} checksum={checksum}"
```

</details>

#### records the current UTF-16 intermediate-allocation baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = memory_utf16_units()
val before = memory_snapshot()
val encoded = utf16_to_utf8(units)
val after = memory_snapshot()
val live_growth = delta(after.live_bytes, before.live_bytes)
val aux_growth = delta(after.aux_live_bytes, before.aux_live_bytes)
val capacity_growth = delta(after.array_capacity_bytes, before.array_capacity_bytes)
expect(encoded.len()).to_be_greater_than(0)
expect(live_growth + aux_growth + capacity_growth).to_be_less_than(67108865)
val status = if counters_available(after): "measured" else: "unavailable"
if status == "unavailable":
    expect(after.live_bytes).to_equal(0)
    expect(after.aux_live_bytes).to_equal(0)
    expect(after.array_capacity_bytes).to_equal(0)
print "text_memory operation=utf16_to_utf8 counter_status={status} input_units={units.len()} output_bytes={encoded.len()} allocation_count=unavailable heap_peak_bytes=unavailable live_growth_bytes={live_growth} aux_growth_bytes={aux_growth} array_capacity_growth_bytes={capacity_growth} live_bytes={after.live_bytes}"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/utf8_internationalized_text_architecture.md`
- **Plan:** `doc/03_plan/perf/utf8_internationalized_text_architecture.md`
- **Design:** `doc/05_design/lib/text_i18n/utf8_internationalized_text_architecture.md`
- **Research:** `doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md`


</details>
