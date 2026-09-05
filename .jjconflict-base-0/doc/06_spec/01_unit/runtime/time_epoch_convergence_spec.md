# Time Clock-Epoch Convergence

> Pins the EPOCH of each runtime time primitive so the engines cannot diverge

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Clock-Epoch Convergence

Pins the EPOCH of each runtime time primitive so the engines cannot diverge

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/time_epoch_convergence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the EPOCH of each runtime time primitive so the engines cannot diverge
again. Discovered by stream G2 (commit `47adbf730ca`) and measured on
2026-08-10: the Rust interpreter's extern table returned WALL-CLOCK for
`rt_time_now_nanos` / `rt_time_now_micros` (~1.786e18) while every other lane
(runtime_native.c, runtime_time.c, unix_common.h, platform_win.h, and the
pure-Simple `src/runtime/simple_core/core_process.spl`) returned
CLOCK_MONOTONIC. A ~50-year gap behind one symbol name.

Contract pinned here (matches `src/runtime/runtime.h:251-252` and the
docstrings in `src/lib/nogc_sync_mut/io/time_ops.spl`):

  * `rt_time_now_nanos`  -> MONOTONIC nanoseconds.  Durations only.
  * `rt_time_now_micros` -> MONOTONIC microseconds. Durations only.
  * `rt_time_now_unix_micros` -> WALL-CLOCK microseconds since the Unix epoch.

Every in-tree caller of the two monotonic names uses the reading as a DELTA
(`now - started`), so monotonic is the correct convergence target and the
wall-clock/absolute split already has a correctly-named home in
`rt_time_now_unix_micros`.

The discriminator is a magnitude band, not a symbol sweep: a wall-clock nanos
reading is ~1.8e18 and a monotonic one is at most a machine uptime (< 1e17,
i.e. under ~3 years of nanoseconds). Swapping the clock source in any lane
moves the reading across that band by ~5 orders of magnitude, so this oracle
cannot pass on the wrong clock.

## Scenarios

### runtime time primitives have pinned, convergent epochs

#### rt_time_now_nanos is MONOTONIC, not wall-clock

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_time_now_nanos is MONOTONIC, not wall-clock
   - Expected: n >= 0 is true
   - Expected: n < MONOTONIC_NANOS_CEILING is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_time_now_nanos is MONOTONIC, not wall-clock")
val n = rt_time_now_nanos()
expect(n >= 0).to_equal(true)
# RED if the lane is wired to CLOCK_REALTIME / SystemTime::UNIX_EPOCH.
expect(n < MONOTONIC_NANOS_CEILING).to_equal(true)
```

</details>

#### rt_time_now_micros is MONOTONIC, not wall-clock

- rt_time_now_micros is MONOTONIC, not wall-clock
   - Expected: u >= 0 is true
   - Expected: u < MONOTONIC_MICROS_CEILING is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_time_now_micros is MONOTONIC, not wall-clock")
val u = rt_time_now_micros()
expect(u >= 0).to_equal(true)
expect(u < MONOTONIC_MICROS_CEILING).to_equal(true)
```

</details>

#### rt_time_now_unix_micros is WALL-CLOCK, not monotonic

- rt_time_now_unix_micros is WALL-CLOCK, not monotonic
   - Expected: w > WALLCLOCK_MICROS_FLOOR is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_time_now_unix_micros is WALL-CLOCK, not monotonic")
# The mirror-image defect: a wall-clock name wired to a monotonic
# source. `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs`
# does exactly this in the native-binary stub lane.
val w = rt_time_now_unix_micros()
expect(w > WALLCLOCK_MICROS_FLOOR).to_equal(true)
```

</details>

#### the monotonic and wall-clock families are separated by their epochs

- the monotonic and wall-clock families are separated by their epochs
   - Expected: wall > mono is true
   - Expected: wall - mono > WALLCLOCK_MICROS_FLOOR / 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the monotonic and wall-clock families are separated by their epochs")
# The whole point of the convergence: the two families must NOT be
# interchangeable, and must be distinguishable at a glance.
val mono = rt_time_now_micros()
val wall = rt_time_now_unix_micros()
expect(wall > mono).to_equal(true)
expect(wall - mono > WALLCLOCK_MICROS_FLOOR / 2).to_equal(true)
```

</details>

#### monotonic readings are non-decreasing and usable as durations

- monotonic readings are non-decreasing and usable as durations
   - Expected: t1 >= t0 is true
   - Expected: t1 - t0 < 3600000000000 is true
   - Expected: spin >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("monotonic readings are non-decreasing and usable as durations")
val t0 = rt_time_now_nanos()
var spin = 0
for i in 0..2000:
    spin = spin + i
val t1 = rt_time_now_nanos()
expect(t1 >= t0).to_equal(true)
# A single spin loop cannot take an hour; catches a lane that mixes
# two different epochs across two calls to the SAME function.
expect(t1 - t0 < 3600000000000).to_equal(true)
expect(spin >= 0).to_equal(true)
```

</details>

#### nanos and micros agree with each other to within a second

- nanos and micros agree with each other to within a second
   - Expected: skew < 1000000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nanos and micros agree with each other to within a second")
# Both must be on the SAME monotonic epoch, not two different ones.
val n = rt_time_now_nanos()
val u = rt_time_now_micros()
var skew = n / 1000 - u
if skew < 0:
    skew = 0 - skew
expect(skew < 1000000).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `33639ae97c8e41157f8ceca10442dfc0c2c5208a99197a5706e62d7eddcfdcea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33639ae97c8e41157f8ceca10442dfc0c2c5208a99197a5706e62d7eddcfdcea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33639ae97c8e41157f8ceca10442dfc0c2c5208a99197a5706e62d7eddcfdcea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/runtime/time_epoch_convergence_spec.spl
mirror: doc/06_spec/01_unit/runtime/time_epoch_convergence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/time_epoch_convergence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/time_epoch_convergence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/time_epoch_convergence_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_time_now_nanos is MONOTONIC, not wall-clock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/time_epoch_convergence_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_time_now_micros is MONOTONIC, not wall-clock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/time_epoch_convergence_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_time_now_unix_micros is WALL-CLOCK, not monotonic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
