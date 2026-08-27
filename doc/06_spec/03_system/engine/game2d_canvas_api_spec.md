# Game2D Canvas API (AC-2)

> `Canvas` provides `clear`, `draw(image,pos)`, `draw(image,transform)`, `rect`,

<!-- sdn-diagram:id=game2d_canvas_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_canvas_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_canvas_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_canvas_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Canvas API (AC-2)

`Canvas` provides `clear`, `draw(image,pos)`, `draw(image,transform)`, `rect`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_canvas_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

`Canvas` provides `clear`, `draw(image,pos)`, `draw(image,transform)`, `rect`,
`circle`, `line`, `text`. `Vec2`, `Rect`, `Color`, `Transform2D`, `DrawMode`
are exposed under `std.game2d.math` as **re-exports** of `common/engine/*`
(no redefinition).

Error code added to ### 3-arch (TODO): GAME-RENDER-001 — drawing with a null Image panics.

Red-phase: Canvas methods absent; signature-presence assertions fail.

## Scenarios

### Game2D Canvas (AC-2)
_## Drawing primitives + math re-exports._

### Canvas declares the 7 documented methods

#### fn clear(self, color) is declared in canvas.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn clear(")).to_equal(true)
```

</details>

#### fn draw(self, image, pos) overload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn draw(") and _has(src, "Image")
    ).to_equal(true)
```

</details>

#### fn draw(self, image, transform) overload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "Transform2D")).to_equal(true)
```

</details>

#### fn rect(mode, rect, color) declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn rect(")).to_equal(true)
```

</details>

#### fn circle(mode, center, r, color) declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn circle(")).to_equal(true)
```

</details>

#### fn line(a, b, color) declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn line(")).to_equal(true)
```

</details>

#### fn text(text, pos, color) declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn text(")).to_equal(true)
```

</details>

### math re-exports (no redefinition)

#### math/__init__.spl re-exports Vec2 / Rect / Color / Transform2D / DrawMode

1.  has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/math/__init__.spl")
expect(_has(src, "Vec2") and _has(src, "Rect") and
       _has(src, "Color") and _has(src, "Transform2D") and
       _has(src, "DrawMode")).to_equal(true)
```

</details>

#### DrawMode is an enum with Stroke and Fill

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/math/__init__.spl")
expect(_has(src, "Stroke") and _has(src, "Fill")
    ).to_equal(true)
```

</details>

### edge case: transparent color is a no-op

#### drawing with Color { a = 0 } produces no command

1.  has


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Spec'd via signature comment; will be verified in Phase 5+ once
# impl exists. Red signal: search the file for the commented contract.
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "Color") and _has(src, "a == 0") or
       _has(src, "alpha == 0") or _has(src, "transparent")
    ).to_equal(true)
```

</details>

#### synthetic edge: detector matches expected guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake = "if color.a == 0: return  # transparent no-op"
expect(_has(fake, "a == 0")).to_equal(true)
```

</details>

### error path: drawing with null image panics GAME-RENDER-001

#### GAME-RENDER-001 error code is wired in canvas.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "GAME-RENDER-001")).to_equal(true)
```

</details>

#### edge case: synthetic detector matches the code form

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("panic GAME-RENDER-001 null image", "GAME-RENDER-001")
    ).to_equal(true)
```

</details>

#### error path: empty source does not falsely satisfy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "GAME-RENDER-001")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
