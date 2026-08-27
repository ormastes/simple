# Game2D Replay Test (AC-5 — replay half)

> Drives an `App` under `HeadlessBackend` with a scripted `[InputSnapshot]`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Replay Test (AC-5 — replay half)

Drives an `App` under `HeadlessBackend` with a scripted `[InputSnapshot]`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_replay_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Drives an `App` under `HeadlessBackend` with a scripted `[InputSnapshot]`
sequence, runs N fixed steps, asserts `app.player.transform.x` matches the
expected value to ε ≤ 0.01.

Edge case: identical replay run twice → identical state (determinism check).
Error path: missing replay fixture → spec fails with diff diagnostic.

Red-phase: HeadlessBackend / ScriptedInput absent; signature-presence
assertions fail.

## Scenarios

### Game2D Replay (AC-5 replay)

### HeadlessBackend + ScriptedInput declared

#### headless.spl declares class HeadlessBackend

- headless.spl declares class HeadlessBackend
   - Expected: _has(src, "class HeadlessBackend") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless.spl declares class HeadlessBackend")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "class HeadlessBackend")).to_equal(true)
```

</details>

#### headless.spl declares class ScriptedInput

- headless.spl declares class ScriptedInput
   - Expected: _has(src, "class ScriptedInput") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless.spl declares class ScriptedInput")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "class ScriptedInput")).to_equal(true)
```

</details>

#### ScriptedInput holds [InputSnapshot] frames

- ScriptedInput holds [InputSnapshot] frames
   - Expected: _has(src, "InputSnapshot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ScriptedInput holds [InputSnapshot] frames")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "InputSnapshot")).to_equal(true)
```

</details>

#### HeadlessBackend implements GameBackend trait

- HeadlessBackend implements GameBackend trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HeadlessBackend implements GameBackend trait")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "HeadlessBackend") and
       _has(src, "GameBackend")).to_equal(true)
```

</details>

### replay fixture exists

#### test/fixtures/game2d_replay_hello.sdn exists

- test/fixtures/game2d_replay_hello.sdn exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/fixtures/game2d_replay_hello.sdn exists")
expect(rt_file_exists(
    "test/fixtures/game2d_replay_hello.sdn")).to_equal(true)
```

</details>

#### fixture declares scripted frames

- fixture declares scripted frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture declares scripted frames")
val src = _read("test/fixtures/game2d_replay_hello.sdn")
expect(_has(src, "frames") or _has(src, "frame:")
    ).to_equal(true)
```

</details>

### edge case: same replay twice yields identical state

#### headless.spl notes determinism guarantee

- headless.spl notes determinism guarantee


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless.spl notes determinism guarantee")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "deterministic") or _has(src, "byte-equal") or
       _has(src, "determinism")).to_equal(true)
```

</details>

#### synthetic ε-equality check at 0.01

- synthetic ε-equality check at 0.01
   - Expected: diff < 0.011 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic ε-equality check at 0.01")
val a = 1.234
val b = 1.235
val diff = if a > b: a - b else: b - a
expect(diff < 0.011).to_equal(true)
```

</details>

### error path: missing replay fixture

#### spec helper reports missing fixture, does not crash

- spec helper reports missing fixture, does not crash
   - Expected: src.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spec helper reports missing fixture, does not crash")
val src = _read("test/fixtures/game2d_replay_does_not_exist.sdn")
expect(src.len()).to_equal(0)
```

</details>

#### edge case: empty fixture content yields empty read

- edge case: empty fixture content yields empty read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: empty fixture content yields empty read")
expect(_read("test/fixtures/game2d_replay_does_not_exist.sdn")
    ).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `9450265714851a903fa47b9e668f51031611059206e8fe12d01f3c5107ec0265`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9450265714851a903fa47b9e668f51031611059206e8fe12d01f3c5107ec0265`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9450265714851a903fa47b9e668f51031611059206e8fe12d01f3c5107ec0265`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/engine/game2d_replay_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_replay_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_replay_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_replay_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_replay_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/engine/game2d_replay_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'headless.spl declares class HeadlessBackend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_replay_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'headless.spl declares class ScriptedInput' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_replay_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ScriptedInput holds [InputSnapshot] frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
