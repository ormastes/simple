# Game2D Deterministic Loop (AC-4)

> 60 Hz fixed-step accumulator: 100ms wall time → exactly 6 fixed_update calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Deterministic Loop (AC-4)

60 Hz fixed-step accumulator: 100ms wall time → exactly 6 fixed_update calls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_deterministic_loop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

60 Hz fixed-step accumulator: 100ms wall time → exactly 6 fixed_update calls.
`#[deterministic]` mode → `g.time.now()` outside callback panics with
`GAME-DET-001`. Inside `update`/`fixed_update` it returns simulated step time.

Red-phase: LoopDriver/det_guard absent; assertions fail until Phase 5.

## Scenarios

### Game2D Deterministic Loop (AC-4)

### LoopDriver fixed-step accumulator

<details>
<summary>Advanced: driver.spl declares class LoopDriver</summary>

#### driver.spl declares class LoopDriver

- driver.spl declares class LoopDriver
   - Expected: _has(src, "class LoopDriver") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver.spl declares class LoopDriver")
val src = _read("src/lib/nogc_sync_mut/game2d/loop/driver.spl")
expect(_has(src, "class LoopDriver")).to_equal(true)
```

</details>


</details>

#### driver.spl wraps Clock.consume_fixed_steps

- driver.spl wraps Clock.consume_fixed_steps
   - Expected: _has(src, "consume_fixed_steps") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver.spl wraps Clock.consume_fixed_steps")
val src = _read("src/lib/nogc_sync_mut/game2d/loop/driver.spl")
expect(_has(src, "consume_fixed_steps")).to_equal(true)
```

</details>

#### driver.spl pumps app.update + app.fixed_update

- driver.spl pumps app.update + app.fixed_update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver.spl pumps app.update + app.fixed_update")
val src = _read("src/lib/nogc_sync_mut/game2d/loop/driver.spl")
expect(_has(src, "fixed_update") and _has(src, "update")
    ).to_equal(true)
```

</details>

#### edge case: synthetic 100ms@60Hz computes 6 steps

- edge case: synthetic 100ms@60Hz computes 6 steps
   - Expected: n_steps equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic 100ms@60Hz computes 6 steps")
# Plain math sanity: 100ms / (1000/60)ms ≈ 6.0
val step_ms = 1000 / 60
val n_steps = 100 / step_ms
expect(n_steps).to_equal(6)
```

</details>

#### edge case: 0ms wall time → 0 fixed_update calls

- edge case: 0ms wall time → 0 fixed_update calls
   - Expected: n_steps equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: 0ms wall time → 0 fixed_update calls")
val step_ms = 1000 / 60
val n_steps = 0 / step_ms
expect(n_steps).to_equal(0)
```

</details>

### det_guard runtime checks

#### det_guard.spl declares fn now and fn rand

- det_guard.spl declares fn now and fn rand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("det_guard.spl declares fn now and fn rand")
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "fn now(") and _has(src, "fn rand(")
    ).to_equal(true)
```

</details>

#### det_guard.spl declares enter_callback / leave_callback

- det_guard.spl declares enter_callback / leave_callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("det_guard.spl declares enter_callback / leave_callback")
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "enter_callback") and
       _has(src, "leave_callback")).to_equal(true)
```

</details>

#### GAME-DET-001 panic code is wired

- GAME-DET-001 panic code is wired
   - Expected: _has(src, "GAME-DET-001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GAME-DET-001 panic code is wired")
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "GAME-DET-001")).to_equal(true)
```

</details>

#### edge case: synthetic detector finds the code

- edge case: synthetic detector finds the code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic detector finds the code")
expect(_has("panic GAME-DET-001 wall clock outside callback",
    "GAME-DET-001")).to_equal(true)
```

</details>

### error path: unseeded random in deterministic mode panics

#### det_guard.spl mentions seeded RNG path

- det_guard.spl mentions seeded RNG path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("det_guard.spl mentions seeded RNG path")
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "seeded") or _has(src, "rng_seed") or
       _has(src, "deterministic")).to_equal(true)
```

</details>

#### edge case: empty source does not falsely satisfy

- edge case: empty source does not falsely satisfy
   - Expected: _has("", "deterministic") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: empty source does not falsely satisfy")
expect(_has("", "deterministic")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d0c2b9a35ba9f018dc78cf75e735bb8223d7c156c1d061a8a6ad880911816b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d0c2b9a35ba9f018dc78cf75e735bb8223d7c156c1d061a8a6ad880911816b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d0c2b9a35ba9f018dc78cf75e735bb8223d7c156c1d061a8a6ad880911816b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/engine/game2d_deterministic_loop_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_deterministic_loop_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_deterministic_loop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_deterministic_loop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_deterministic_loop_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/engine/game2d_deterministic_loop_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver.spl declares class LoopDriver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_deterministic_loop_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver.spl wraps Clock.consume_fixed_steps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_deterministic_loop_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver.spl pumps app.update + app.fixed_update' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
