# time_spec

> Test suite for the std.time module, verifying time measurement and sleep functionality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# time_spec

Test suite for the std.time module, verifying time measurement and sleep functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/time_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Test suite for the std.time module, verifying time measurement and sleep functionality.

## Scenarios

### Time Module

#### Time measurement

#### now_micros returns positive microseconds

- now_micros returns positive microseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("now_micros returns positive microseconds")
val micros = time_now_micros()
expect micros > 0
```

</details>

#### now_nanos returns positive nanoseconds

- now_nanos returns positive nanoseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("now_nanos returns positive nanoseconds")
val nanos = time_now_nanos()
expect nanos > 0
```

</details>

#### now_ms returns positive milliseconds

- now_ms returns positive milliseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("now_ms returns positive milliseconds")
val ms = time_now_ms()
expect ms > 0
```

</details>

#### now returns positive seconds

- now returns positive seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("now returns positive seconds")
val secs = time_now()
expect secs > 0.0
```

</details>

#### nanos is approximately micros * 1000

- nanos is approximately micros * 1000


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nanos is approximately micros * 1000")
val micros = time_now_micros()
val nanos = time_now_nanos()
# Should be within same millisecond (allowing for execution time)
val diff = (nanos / 1000) - micros
expect diff.abs() < 1000  # Within 1ms
```

</details>

#### ms is approximately micros / 1000

- ms is approximately micros / 1000


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ms is approximately micros / 1000")
val micros = time_now_micros()
val ms = time_now_ms()
val diff = micros / 1000 - ms
expect diff.abs() < 2  # Within 2ms
```

</details>

#### elapsed time increases

- elapsed time increases


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elapsed time increases")
val start = time_now_micros()
# Busy wait a bit
var x = 0
for i in 0..1000:
    x = x + i
val end = time_now_micros()
expect end > start
```

</details>

#### elapsed time is measurable

- elapsed time is measurable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elapsed time is measurable")
val start = time_now()
# Busy wait
var x = 0
for i in 0..10000:
    x = x + i
val elapsed = time_now() - start
expect elapsed > 0.0
```

</details>

#### Sleep functions

#### sleep pauses execution for specified duration

- sleep pauses execution for specified duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep pauses execution for specified duration")
val start = time_now()
time_sleep(0.1)  # Sleep 100ms
val elapsed = time_now() - start
# Should be at least 100ms (0.1s)
# Allow up to 150ms due to OS scheduler
expect elapsed >= 0.09
expect elapsed <= 0.2
```

</details>

#### sleep_ms pauses for milliseconds

- sleep_ms pauses for milliseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep_ms pauses for milliseconds")
val start = time_now_ms()
time_sleep_ms(50)
val elapsed = time_now_ms() - start
expect elapsed >= 45  # At least 45ms
expect elapsed <= 100  # At most 100ms
```

</details>

#### sleep with zero duration does not crash

- sleep with zero duration does not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep with zero duration does not crash")
time_sleep(0.0)
# Should complete without error
```

</details>

#### sleep_micros with small duration works

- sleep_micros with small duration works


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep_micros with small duration works")
val start = time_now_micros()
time_sleep_micros(1000)  # 1ms
val elapsed = time_now_micros() - start
expect elapsed >= 500  # At least 0.5ms
expect elapsed <= 5000  # At most 5ms
```

</details>

#### Time conversions

#### microseconds to milliseconds conversion

- microseconds to milliseconds conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("microseconds to milliseconds conversion")
val micros: i64 = 1000000  # 1 million microseconds
val ms = micros / 1000
expect ms == 1000  # 1000 milliseconds
```

</details>

#### milliseconds to seconds conversion

- milliseconds to seconds conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("milliseconds to seconds conversion")
val ms: i64 = 5000
val secs = ms as f64 / 1000.0
expect secs == 5.0
```

</details>

#### nanoseconds to microseconds approximation

- nanoseconds to microseconds approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nanoseconds to microseconds approximation")
val nanos: i64 = 1000000  # 1 million nanoseconds
val micros = nanos / 1000
expect micros == 1000
```

</details>

#### Edge cases

#### now functions work multiple times

- now functions work multiple times


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("now functions work multiple times")
val t1 = time_now_micros()
val t2 = time_now_micros()
val t3 = time_now_micros()
expect t3 >= t2
expect t2 >= t1
```

</details>

#### time values are monotonic

- time values are monotonic


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("time values are monotonic")
var prev = time_now_micros()
for _ in 0..10:
    val curr = time_now_micros()
    expect curr >= prev
    prev = curr
```

</details>

#### very short sleep does not panic

- very short sleep does not panic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("very short sleep does not panic")
time_sleep(0.001)  # 1ms
time_sleep_micros(100)  # 100 microseconds
# Should complete without error
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `1d410f31436236018eb01de97a50b561e0a3575c17fe1ca8aa24363b444633f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d410f31436236018eb01de97a50b561e0a3575c17fe1ca8aa24363b444633f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d410f31436236018eb01de97a50b561e0a3575c17fe1ca8aa24363b444633f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/std/time_spec.spl
mirror: doc/06_spec/unit/lib/std/time_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/time_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/time_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/time_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'now_micros returns positive microseconds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/time_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'now_nanos returns positive nanoseconds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/time_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'now_ms returns positive milliseconds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
