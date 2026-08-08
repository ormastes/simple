# Game2D InputSnapshot (AC-3)

> Snapshot-based input view: `g.input.key_down(K)`, `key_pressed_this_frame(K)`,

<!-- sdn-diagram:id=game2d_input_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_input_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_input_snapshot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_input_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D InputSnapshot (AC-3)

Snapshot-based input view: `g.input.key_down(K)`, `key_pressed_this_frame(K)`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_input_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Snapshot-based input view: `g.input.key_down(K)`, `key_pressed_this_frame(K)`,
`mouse_pos()`, `mouse_down(B)` backed by `class InputSnapshot {
keys_down, keys_pressed, mouse_pos, mouse_buttons }`.

Archtest: examples/11_advanced/game2d/** must NOT call rt_sdl2_* directly — the snapshot
is the only read path.

Red-phase: InputSnapshot/api absent; signature-presence assertions fail.

## Scenarios

### Game2D InputSnapshot (AC-3)
_## Frame-frozen snapshot input._

### InputSnapshot class declared

#### snapshot.spl declares class InputSnapshot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/input/snapshot.spl")
expect(_has(src, "class InputSnapshot")).to_equal(true)
```

</details>

#### InputSnapshot has keys_down/keys_pressed/mouse_pos/mouse_buttons

1.  has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/input/snapshot.spl")
expect(_has(src, "keys_down") and _has(src, "keys_pressed") and
       _has(src, "mouse_pos") and _has(src, "mouse_buttons")
    ).to_equal(true)
```

</details>

#### edge case: synthetic class declaration is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "class InputSnapshot:\n    var keys_down: [Key]\n"
expect(_has(sample, "class InputSnapshot")).to_equal(true)
```

</details>

### g.input accessors

#### api.spl declares fn key_down(k: Key) -> bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/input/api.spl")
expect(_has(src, "fn key_down(") and _has(src, "Key")
    ).to_equal(true)
```

</details>

#### api.spl declares fn key_pressed_this_frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/input/api.spl")
expect(_has(src, "fn key_pressed_this_frame(")).to_equal(true)
```

</details>

#### api.spl declares fn mouse_pos and fn mouse_down

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/input/api.spl")
expect(_has(src, "fn mouse_pos(") and _has(src, "fn mouse_down(")
    ).to_equal(true)
```

</details>

### edge case: simultaneous press+release in same frame

#### snapshot retains the press in keys_pressed

1.  has


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Contract documented in snapshot.spl header; red until impl.
val src = _read("src/lib/nogc_sync_mut/game2d/input/snapshot.spl")
expect(_has(src, "press") and _has(src, "release") or
       _has(src, "keys_pressed_this_frame") or
       _has(src, "frame-coalesced")).to_equal(true)
```

</details>

#### synthetic: detector finds 'frame-coalesced' marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("# frame-coalesced press wins", "frame-coalesced")
    ).to_equal(true)
```

</details>

### error path: no direct OS input calls in user code

#### examples/11_advanced/game2d/hello/main.spl does not call rt_sdl2_*

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_has(src, "rt_sdl2_")).to_equal(false)
```

</details>

#### examples/11_advanced/game2d/hello/main.spl does not import std.io

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_has(src, "use std.nogc_sync_mut.io")).to_equal(false)
```

</details>

#### edge case: synthetic violation is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("rt_sdl2_is_key_pressed(...)", "rt_sdl2_")
    ).to_equal(true)
```

</details>

#### error path: empty content does not falsely flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "rt_sdl2_")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
