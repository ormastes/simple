# Game2D Canvas API (AC-2)

> `Canvas` provides `clear`, `draw(image,pos)`, `draw(image,transform)`, `rect`,

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`Canvas` provides `clear`, `draw(image,pos)`, `draw(image,transform)`, `rect`,
`circle`, `line`, `text`. `Vec2`, `Rect`, `Color`, `Transform2D`, `DrawMode`
are exposed under `std.game2d.math` as **re-exports** of `common/engine/*`
(no redefinition).

Error code added to ### 3-arch (TODO): GAME-RENDER-001 — drawing with a null Image panics.

Red-phase: Canvas methods absent; signature-presence assertions fail.

## Scenarios

### Game2D Canvas (AC-2)

### Canvas declares the 7 documented methods

#### fn clear(self, color) is declared in canvas.spl

- fn clear(self, color) is declared in canvas.spl
   - Expected: _has(src, "fn clear(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn clear(self, color) is declared in canvas.spl")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn clear(")).to_equal(true)
```

</details>

#### fn draw(self, image, pos) overload

- fn draw(self, image, pos) overload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn draw(self, image, pos) overload")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn draw(") and _has(src, "Image")
    ).to_equal(true)
```

</details>

#### fn draw(self, image, transform) overload

- fn draw(self, image, transform) overload
   - Expected: _has(src, "Transform2D") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn draw(self, image, transform) overload")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "Transform2D")).to_equal(true)
```

</details>

#### fn rect(mode, rect, color) declared

- fn rect(mode, rect, color) declared
   - Expected: _has(src, "fn rect(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn rect(mode, rect, color) declared")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn rect(")).to_equal(true)
```

</details>

#### fn circle(mode, center, r, color) declared

- fn circle(mode, center, r, color) declared
   - Expected: _has(src, "fn circle(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn circle(mode, center, r, color) declared")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn circle(")).to_equal(true)
```

</details>

#### fn line(a, b, color) declared

- fn line(a, b, color) declared
   - Expected: _has(src, "fn line(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn line(a, b, color) declared")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn line(")).to_equal(true)
```

</details>

#### fn text(text, pos, color) declared

- fn text(text, pos, color) declared
   - Expected: _has(src, "fn text(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fn text(text, pos, color) declared")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "fn text(")).to_equal(true)
```

</details>

### math re-exports (no redefinition)

#### math/__init__.spl re-exports Vec2 / Rect / Color / Transform2D / DrawMode

- math/__init__.spl re-exports Vec2 / Rect / Color / Transform2D / DrawMode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("math/__init__.spl re-exports Vec2 / Rect / Color / Transform2D / DrawMode")
val src = _read("src/lib/nogc_sync_mut/game2d/math/__init__.spl")
expect(_has(src, "Vec2") and _has(src, "Rect") and
       _has(src, "Color") and _has(src, "Transform2D") and
       _has(src, "DrawMode")).to_equal(true)
```

</details>

#### DrawMode is an enum with Stroke and Fill

- DrawMode is an enum with Stroke and Fill


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("DrawMode is an enum with Stroke and Fill")
val src = _read("src/lib/nogc_sync_mut/game2d/math/__init__.spl")
expect(_has(src, "Stroke") and _has(src, "Fill")
    ).to_equal(true)
```

</details>

### edge case: transparent color is a no-op

#### drawing with Color { a = 0 } produces no command

- drawing with Color { a = 0 } produces no command


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drawing with Color { a = 0 } produces no command")
# Spec'd via signature comment; will be verified in Phase 5+ once
# impl exists. Red signal: search the file for the commented contract.
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "Color") and _has(src, "a == 0") or
       _has(src, "alpha == 0") or _has(src, "transparent")
    ).to_equal(true)
```

</details>

#### synthetic edge: detector matches expected guard

- synthetic edge: detector matches expected guard
   - Expected: _has(fake, "a == 0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic edge: detector matches expected guard")
val fake = "if color.a == 0: return  # transparent no-op"
expect(_has(fake, "a == 0")).to_equal(true)
```

</details>

### error path: drawing with null image panics GAME-RENDER-001

#### GAME-RENDER-001 error code is wired in canvas.spl

- GAME-RENDER-001 error code is wired in canvas.spl
   - Expected: _has(src, "GAME-RENDER-001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GAME-RENDER-001 error code is wired in canvas.spl")
val src = _read("src/lib/nogc_sync_mut/game2d/render/canvas.spl")
expect(_has(src, "GAME-RENDER-001")).to_equal(true)
```

</details>

#### edge case: synthetic detector matches the code form

- edge case: synthetic detector matches the code form


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic detector matches the code form")
expect(_has("panic GAME-RENDER-001 null image", "GAME-RENDER-001")
    ).to_equal(true)
```

</details>

#### error path: empty source does not falsely satisfy

- error path: empty source does not falsely satisfy
   - Expected: _has("", "GAME-RENDER-001") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path: empty source does not falsely satisfy")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c75defe4e8659a417dcfa2247dbc8084ebd927249f197e94e591bee707e183d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c75defe4e8659a417dcfa2247dbc8084ebd927249f197e94e591bee707e183d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c75defe4e8659a417dcfa2247dbc8084ebd927249f197e94e591bee707e183d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/game2d_canvas_api_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_canvas_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_canvas_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_canvas_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_canvas_api_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fn clear(self, color) is declared in canvas.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_canvas_api_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fn draw(self, image, pos) overload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_canvas_api_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fn draw(self, image, transform) overload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
