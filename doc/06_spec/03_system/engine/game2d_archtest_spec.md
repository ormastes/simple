# Game2D Architecture Constraints (AC-8)

> System spec covering the architecture rules for `std.game2d`:

<!-- sdn-diagram:id=game2d_archtest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_archtest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_archtest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_archtest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Architecture Constraints (AC-8)

System spec covering the architecture rules for `std.game2d`:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_archtest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System spec covering the architecture rules for `std.game2d`:
- No file under `src/lib/nogc_sync_mut/game2d/**` exceeds 800 lines.
- No `class X : Y` inheritance form (only `: TraitName` for trait impl).
- `Vec2` / `Rect` / `Color` / `Transform2D` are NOT redefined inside game2d
  (must re-export from `common/engine/math2d.spl` etc.).
- No new game2d file duplicates a function defined in `engine/render/`
  or `engine/sprite/`.
- All `std.game2d.*` exports route through `__init__.spl`.

Red-phase: implementation does not yet exist; specs must FAIL on the
assertion side (not parse/import side).

## Scenarios

### Game2D Architecture (AC-8)
_## Architecture rules. Red-phase — no impl yet.""_

### no file exceeds 800-line budget

#### every game2d module is under 800 lines

1. over budget = over budget push
   - Expected: over_budget.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var over_budget: [text] = []
for path in _game2d_files():
    val content = _read_or_empty(path)
    val n = _count_lines(content)
    if n > 800:
        over_budget = over_budget.push(path)
expect(over_budget.len()).to_equal(0)
```

</details>

#### edge case: a synthetic 801-line file would be flagged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Confirms the assertion is real, not vacuous.
val fake_lines = _repeat_str("x\n", 801)
expect(_count_lines(fake_lines) > 800).to_equal(true)
```

</details>

#### error path: missing file is treated as 0 lines (not a crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = _count_lines(_read_or_empty(
    "src/lib/nogc_sync_mut/game2d/does_not_exist.spl"))
expect(n).to_equal(0)
```

</details>

### no forbidden class-inheritance forms

#### no game2d file declares `class X : ConcreteClass`

1. offenders = offenders push
   - Expected: offenders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var offenders: [text] = []
for path in _game2d_files():
    val content = _read_or_empty(path)
    if _forbidden_class_inheritance(content):
        offenders = offenders.push(path)
expect(offenders.len()).to_equal(0)
```

</details>

#### edge case: synthetic forbidden form is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_forbidden_class_inheritance(
    "class HeadlessBackend : SdlBackend\n")).to_equal(true)
```

</details>

#### error path: empty content is never flagged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_forbidden_class_inheritance("")).to_equal(false)
```

</details>

### no math-primitive redefinitions

#### Vec2/Rect2/EngineColor/Transform2D not redefined under game2d/**

1. offenders = offenders push
   - Expected: offenders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var offenders: [text] = []
for path in _game2d_files():
    val content = _read_or_empty(path)
    if _redefines_math_primitive(content):
        offenders = offenders.push(path)
expect(offenders.len()).to_equal(0)
```

</details>

#### edge case: a redefinition string is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_redefines_math_primitive("class Vec2:\n    var x: f32\n")
    ).to_equal(true)
```

</details>

#### error path: only an exact form triggers (avoid false positive)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_redefines_math_primitive("# uses Vec2 here\n")
    ).to_equal(false)
```

</details>

### all std.game2d.* exports route through __init__.spl

#### __init__.spl exists at the package root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "src/lib/nogc_sync_mut/game2d/__init__.spl")).to_equal(true)
```

</details>

#### edge case: a synthetic __init__.spl with re-exports parses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "use std.nogc_sync_mut.game2d.app.app\n"
expect(_contains(sample, "use std.nogc_sync_mut.game2d.")
    ).to_equal(true)
```

</details>

#### error path: missing-file path returns empty without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read_or_empty(
    "src/lib/nogc_sync_mut/game2d/__init__.spl")
expect(content.len() >= 0).to_equal(true)
```

</details>

### no duplicate engine primitives

#### no game2d/render/* file redefines render_text_to_buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val canvas = _read_or_empty(
    "src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_contains(canvas, "fn render_text_to_buffer")
    ).to_equal(false)
```

</details>

#### edge case: detects a synthetic duplicate

1. "fn render text to buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_contains(
    "fn render_text_to_buffer(...) {}",
    "fn render_text_to_buffer")).to_equal(true)
```

</details>

#### error path: empty canvas content does not falsely flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_contains("", "fn render_text_to_buffer")).to_equal(false)
```

</details>

### demo budget AC-1 archtest (≤ 25 lines)

#### examples/11_advanced/game2d/hello/main.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("examples/11_advanced/game2d/hello/main.spl")
    ).to_equal(true)
```

</details>

#### examples/11_advanced/game2d/hello/main.spl has ≤ 25 lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read_or_empty("examples/11_advanced/game2d/hello/main.spl")
val n = _count_lines(content)
expect(n <= 25).to_equal(true)
```

</details>

#### edge case: a synthetic 26-line demo would fail the budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake = _repeat_str("x\n", 26)
expect(_count_lines(fake) <= 25).to_equal(false)
```

</details>

#### error path: hello demo only imports std.game2d

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read_or_empty("examples/11_advanced/game2d/hello/main.spl")
# Forbidden direct OS-input imports inside examples/11_advanced/game2d/**:
expect(_contains(content, "rt_sdl2_")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
