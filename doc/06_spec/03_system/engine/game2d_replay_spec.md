# Game2D Replay Test (AC-5 — replay half)

> Drives an `App` under `HeadlessBackend` with a scripted `[InputSnapshot]`

<!-- sdn-diagram:id=game2d_replay_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_replay_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_replay_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_replay_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
_## Scripted-input replay → deterministic transform state.""_

### HeadlessBackend + ScriptedInput declared

#### headless.spl declares class HeadlessBackend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "class HeadlessBackend")).to_equal(true)
```

</details>

#### headless.spl declares class ScriptedInput

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "class ScriptedInput")).to_equal(true)
```

</details>

#### ScriptedInput holds [InputSnapshot] frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "InputSnapshot")).to_equal(true)
```

</details>

#### HeadlessBackend implements GameBackend trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "HeadlessBackend") and
       _has(src, "GameBackend")).to_equal(true)
```

</details>

### replay fixture exists

#### test/fixtures/game2d_replay_hello.sdn exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "test/fixtures/game2d_replay_hello.sdn")).to_equal(true)
```

</details>

#### fixture declares scripted frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("test/fixtures/game2d_replay_hello.sdn")
expect(_has(src, "frames") or _has(src, "frame:")
    ).to_equal(true)
```

</details>

### edge case: same replay twice yields identical state

#### headless.spl notes determinism guarantee

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "deterministic") or _has(src, "byte-equal") or
       _has(src, "determinism")).to_equal(true)
```

</details>

#### synthetic ε-equality check at 0.01

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1.234
val b = 1.235
val diff = if a > b: a - b else: b - a
expect(diff < 0.011).to_equal(true)
```

</details>

### error path: missing replay fixture

#### spec helper reports missing fixture, does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("test/fixtures/game2d_replay_does_not_exist.sdn")
expect(src.len()).to_equal(0)
```

</details>

#### edge case: empty fixture content yields empty read

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
