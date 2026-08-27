# Perf Stats Specification

> Tests covering perf_stats — statistics harness self-test (sabotage), perf_stats — real p50/p95 for registered SIMD kernels vs scalar (N independent trials, JIT engine via bin/simple run).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Perf Stats Specification

## Scenarios

### perf_stats — statistics harness self-test (sabotage)

#### computes a real p50/p95 that is NOT the mean, and p95 is outlier-sensitive

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes a real p50/p95 that is NOT the mean, and p95 is outlier-sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes a real p50/p95 that is NOT the mean, and p95 is outlier-sensitive")
# 9 clean values around 100us plus one deliberate 10000us outlier.
var trials: [i64] = [100, 101, 99, 102, 98, 100, 103, 97, 100, 10000]
val p50 = perf_stats_p50(trials)
val p95 = perf_stats_p95(trials)
val mean = (100+101+99+102+98+100+103+97+100+10000) / 10
# p50 ignores the tail outlier entirely — stays near the clean cluster.
assert_true(p50 >= 97 and p50 <= 103)
# p95 is dragged by the outlier at n=10 (index 9 -> the outlier itself).
assert_true(p95 == 10000)
# Neither equals the naive mean (1108) — proves this isn't a mean in disguise.
assert_true(p50 != mean)
assert_true(p95 != mean)
print("sabotage-test: p50=" + p50.to_text() + " p95=" + p95.to_text() + " mean=" + mean.to_text())
```

</details>

#### sort is a genuine ascending sort, not an identity pass-through

- sort is a genuine ascending sort, not an identity pass-through


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sort is a genuine ascending sort, not an identity pass-through")
val s = perf_stats_sort_i64([5, 3, 9, 1, 7])
assert_true(s[0] == 1 and s[1] == 3 and s[2] == 5 and s[3] == 7 and s[4] == 9)
```

</details>

### perf_stats — real p50/p95 for registered SIMD kernels vs scalar (N independent trials, JIT engine via bin/simple run)

#### src_over_const: N independent trials x M inner iters at 4096px

- src_over_const: N independent trials x M inner iters at 4096px


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_const: N independent trials x M inner iters at 4096px")
var scalar_trials: [i64] = []
var simd_trials: [i64] = []
var t: i64 = 0
while t < TRIALS:
    var buf_s = filled_random(N, 555 + t)
    val ts0 = time_now_unix_micros()
    var k0: i64 = 0
    while k0 < INNER_ITERS:
        oracle_src_over_const(buf_s, 0, N, 0x40203040)
        k0 = k0 + 1
    val ts1 = time_now_unix_micros()
    scalar_trials.push(ts1 - ts0)

    var buf_v = filled_random(N, 555 + t)
    val tv0 = time_now_unix_micros()
    var k1: i64 = 0
    while k1 < INNER_ITERS:
        simd_isa_src_over_const(buf_v, 0, N, 0x40203040)
        k1 = k1 + 1
    val tv1 = time_now_unix_micros()
    simd_trials.push(tv1 - tv0)
    t = t + 1

val scalar_p50 = perf_stats_p50(scalar_trials)
val scalar_p95 = perf_stats_p95(scalar_trials)
val simd_p50 = perf_stats_p50(simd_trials)
val simd_p95 = perf_stats_p95(simd_trials)
val win_pct = perf_stats_pct_win(scalar_p50, simd_p50)
print("src_over_const p50/p95 us (n=" + TRIALS.to_text() + " trials x " + INNER_ITERS.to_text()
    + " iters): scalar_p50=" + scalar_p50.to_text() + " scalar_p95=" + scalar_p95.to_text()
    + " simd_p50=" + simd_p50.to_text() + " simd_p95=" + simd_p95.to_text()
    + " win_pct=" + win_pct.to_text() + " rss=ABSENT-no-primitive")
assert_true(scalar_p50 >= 0 and simd_p50 >= 0)
```

</details>

#### src_over_image: N independent trials x M inner iters at 4096px

- src_over_image: N independent trials x M inner iters at 4096px


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_image: N independent trials x M inner iters at 4096px")
var scalar_trials: [i64] = []
var simd_trials: [i64] = []
var src = filled_random(N, 777)
var t: i64 = 0
while t < TRIALS:
    var buf_s = filled_random(N, 666 + t)
    val ts0 = time_now_unix_micros()
    var k0: i64 = 0
    while k0 < INNER_ITERS:
        oracle_src_over_image(buf_s, 0, src, 0, N)
        k0 = k0 + 1
    val ts1 = time_now_unix_micros()
    scalar_trials.push(ts1 - ts0)

    var buf_v = filled_random(N, 666 + t)
    val tv0 = time_now_unix_micros()
    var k1: i64 = 0
    while k1 < INNER_ITERS:
        simd_isa_src_over_image(buf_v, 0, src, 0, N)
        k1 = k1 + 1
    val tv1 = time_now_unix_micros()
    simd_trials.push(tv1 - tv0)
    t = t + 1

val scalar_p50 = perf_stats_p50(scalar_trials)
val scalar_p95 = perf_stats_p95(scalar_trials)
val simd_p50 = perf_stats_p50(simd_trials)
val simd_p95 = perf_stats_p95(simd_trials)
val win_pct = perf_stats_pct_win(scalar_p50, simd_p50)
print("src_over_image p50/p95 us (n=" + TRIALS.to_text() + " trials x " + INNER_ITERS.to_text()
    + " iters): scalar_p50=" + scalar_p50.to_text() + " scalar_p95=" + scalar_p95.to_text()
    + " simd_p50=" + simd_p50.to_text() + " simd_p95=" + simd_p95.to_text()
    + " win_pct=" + win_pct.to_text() + " rss=ABSENT-no-primitive")
assert_true(scalar_p50 >= 0 and simd_p50 >= 0)
```

</details>

#### mask_src_over: N independent trials x M inner iters at 4096px

- mask_src_over: N independent trials x M inner iters at 4096px


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mask_src_over: N independent trials x M inner iters at 4096px")
var scalar_trials: [i64] = []
var simd_trials: [i64] = []
var mask = filled_random(N, 999)
var t: i64 = 0
while t < TRIALS:
    var buf_s = filled_random(N, 888 + t)
    val ts0 = time_now_unix_micros()
    var k0: i64 = 0
    while k0 < INNER_ITERS:
        oracle_mask_src_over(buf_s, 0, 0x60778899, mask, 0, N)
        k0 = k0 + 1
    val ts1 = time_now_unix_micros()
    scalar_trials.push(ts1 - ts0)

    var buf_v = filled_random(N, 888 + t)
    val tv0 = time_now_unix_micros()
    var k1: i64 = 0
    while k1 < INNER_ITERS:
        simd_isa_mask_src_over(buf_v, 0, 0x60778899, mask, 0, N)
        k1 = k1 + 1
    val tv1 = time_now_unix_micros()
    simd_trials.push(tv1 - tv0)
    t = t + 1

val scalar_p50 = perf_stats_p50(scalar_trials)
val scalar_p95 = perf_stats_p95(scalar_trials)
val simd_p50 = perf_stats_p50(simd_trials)
val simd_p95 = perf_stats_p95(simd_trials)
val win_pct = perf_stats_pct_win(scalar_p50, simd_p50)
print("mask_src_over p50/p95 us (n=" + TRIALS.to_text() + " trials x " + INNER_ITERS.to_text()
    + " iters): scalar_p50=" + scalar_p50.to_text() + " scalar_p95=" + scalar_p95.to_text()
    + " simd_p50=" + simd_p50.to_text() + " simd_p95=" + simd_p95.to_text()
    + " win_pct=" + win_pct.to_text() + " rss=ABSENT-no-primitive")
assert_true(scalar_p50 >= 0 and simd_p50 >= 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/perf/perf_stats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering perf_stats — statistics harness self-test (sabotage), perf_stats — real p50/p95 for registered SIMD kernels vs scalar (N independent trials, JIT engine via bin/simple run).
- perf_stats — statistics harness self-test (sabotage)
- perf_stats — real p50/p95 for registered SIMD kernels vs scalar (N independent trials, JIT engine via bin/simple run)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c4e316c1fcf2454d155366f7b33e078f98cfefcafd3ebff5410cd1c8ce9db04`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c4e316c1fcf2454d155366f7b33e078f98cfefcafd3ebff5410cd1c8ce9db04`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c4e316c1fcf2454d155366f7b33e078f98cfefcafd3ebff5410cd1c8ce9db04`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/perf/perf_stats_spec.spl
mirror: doc/06_spec/01_unit/lib/common/perf/perf_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/perf/perf_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/perf/perf_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/perf/perf_stats_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes a real p50/p95 that is NOT the mean, and p95 is outlier-sensitive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/perf/perf_stats_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sort is a genuine ascending sort, not an identity pass-through' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/perf/perf_stats_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'src_over_const: N independent trials x M inner iters at 4096px' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
