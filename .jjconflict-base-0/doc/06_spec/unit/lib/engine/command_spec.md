# command_spec

> Engine RenderCommand & RenderCommandBuffer Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# command_spec

Engine RenderCommand & RenderCommandBuffer Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine RenderCommand & RenderCommandBuffer Tests

Tests enum variant construction, buffer creation, and push/clear operations.

## Scenarios

### RenderCommand

### Clear

#### constructs with a color

- constructs with a color
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with a color")
val cmd = RenderCommand.Clear(color: EngineColor.black())
# If we get here without error, construction succeeded
expect(1).to_equal(1)
```

</details>

#### constructs with a non-black color

- constructs with a non-black color
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with a non-black color")
val cmd = RenderCommand.Clear(color: EngineColor.red())
expect(1).to_equal(1)
```

</details>

### DrawRect

#### constructs with Rect2, EngineColor, and ZIndex

- constructs with Rect2, EngineColor, and ZIndex
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with Rect2, EngineColor, and ZIndex")
val rect = Rect2.new(10.0, 20.0, 100.0, 50.0)
val color = EngineColor.red()
val z = ZIndex(value: 5)
val cmd = RenderCommand.DrawRect(rect: rect, color: color, z_order: z)
expect(1).to_equal(1)
```

</details>

#### constructs with zero z_order

- constructs with zero z_order
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with zero z_order")
val rect = Rect2.new(0.0, 0.0, 1.0, 1.0)
val cmd = RenderCommand.DrawRect(
    rect: rect,
    color: EngineColor.white(),
    z_order: ZIndex(value: 0)
)
expect(1).to_equal(1)
```

</details>

### DrawCircle

#### constructs with center, radius, color, and z_order

- constructs with center, radius, color, and z_order
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with center, radius, color, and z_order")
val cmd = RenderCommand.DrawCircle(
    cx: 50.0,
    cy: 60.0,
    radius: 25.0,
    color: EngineColor.green(),
    z_order: ZIndex(value: 1)
)
expect(1).to_equal(1)
```

</details>

### DrawLine

#### constructs with endpoints, width, color, and z_order

- constructs with endpoints, width, color, and z_order
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with endpoints, width, color, and z_order")
val cmd = RenderCommand.DrawLine(
    x1: 0.0,
    y1: 0.0,
    x2: 100.0,
    y2: 100.0,
    width: 2.0,
    color: EngineColor.blue(),
    z_order: ZIndex(value: 3)
)
expect(1).to_equal(1)
```

</details>

### DrawSprite

#### constructs with texture_id, src/dst rects, tint, and z_order

- constructs with texture_id, src/dst rects, tint, and z_order
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with texture_id, src/dst rects, tint, and z_order")
val tex = TextureId(raw: RawHandle.new(0, 1))
val src = Rect2.new(0.0, 0.0, 32.0, 32.0)
val dst = Rect2.new(100.0, 100.0, 64.0, 64.0)
val cmd = RenderCommand.DrawSprite(
    texture_id: tex,
    src_rect: src,
    dst_rect: dst,
    tint: EngineColor.white(),
    z_order: ZIndex(value: 10)
)
expect(1).to_equal(1)
```

</details>

### DrawTriangles

#### constructs with vertices, indices, color, and z_order

- constructs with vertices, indices, color, and z_order
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with vertices, indices, color, and z_order")
val v0 = Vertex2D(x: 0.0, y: 0.0, u: 0.0, v: 0.0, r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val v1 = Vertex2D(x: 10.0, y: 0.0, u: 1.0, v: 0.0, r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val v2 = Vertex2D(x: 5.0, y: 10.0, u: 0.5, v: 1.0, r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val verts: [Vertex2D] = [v0, v1, v2]
val idxs: [i64] = [0, 1, 2]
val cmd = RenderCommand.DrawTriangles(
    vertices: verts,
    indices: idxs,
    color: EngineColor.yellow(),
    z_order: ZIndex(value: 2)
)
expect(1).to_equal(1)
```

</details>

### RenderCommandBuffer

#### starts empty after create

- starts empty after create
   - Expected: buf.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty after create")
val buf = RenderCommandBuffer.create()
expect(buf.len()).to_equal(0)
```

</details>

#### increases length after push

- increases length after push
   - Expected: buf.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increases length after push")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.black()))
expect(buf.len()).to_equal(1)
```

</details>

#### tracks multiple pushes

- tracks multiple pushes
   - Expected: buf.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks multiple pushes")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.black()))
buf.push(RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 0)
))
buf.push(RenderCommand.DrawCircle(
    cx: 5.0, cy: 5.0, radius: 3.0,
    color: EngineColor.blue(),
    z_order: ZIndex(value: 1)
))
expect(buf.len()).to_equal(3)
```

</details>

#### clears all commands

- clears all commands
   - Expected: buf.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all commands")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.white()))
buf.push(RenderCommand.Clear(color: EngineColor.red()))
buf.clear()
expect(buf.len()).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f9bc7ef8c2aa7915785393cc910a381b9a6f4f29fe53d42137d06e9328d60e82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9bc7ef8c2aa7915785393cc910a381b9a6f4f29fe53d42137d06e9328d60e82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9bc7ef8c2aa7915785393cc910a381b9a6f4f29fe53d42137d06e9328d60e82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/engine/command_spec.spl
mirror: doc/06_spec/unit/lib/engine/command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/engine/command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/engine/command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/engine/command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/engine/command_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with a color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/command_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with a non-black color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/command_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with Rect2, EngineColor, and ZIndex' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
