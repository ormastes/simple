# backend_software_primitives_spec

> Software Backend Primitive Rendering Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_software_primitives_spec

Software Backend Primitive Rendering Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Software Backend Primitive Rendering Specification

@tag: gpu, engine2d, software, rendering
@cover src/lib/gc_async_mut/gpu/engine2d/backend_software.spl 40%

Regression guard for the self-pass-to-free-fn mutation-loss bug
(doc/08_tracking/bug/self_pass_to_free_fn_mutation_loss_2026-05-29.md).

Every primitive must write pixels to the framebuffer, not just
draw_rect_filled. Before the fix, circle/line/gradient/rounded/text
delegated to free helper functions that received `self`/`self.buf` as a
parameter, so their writes were silently dropped and only draw_rect_filled
(which writes self.buf inline) rendered anything.

## Scenarios

### SoftwareBackend primitive rendering

#### draw_image preserves each source row in a one-column clipped blit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- draw_image preserves each source row in a one-column clipped blit
   - Expected: p[0 * 4 + 1] equals `BG`
   - Expected: p[1 * 4 + 1] equals `0xFF00FF00u32`
   - Expected: p[2 * 4 + 1] equals `0xFF0000FFu32`
   - Expected: p[3 * 4 + 1] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_image preserves each source row in a one-column clipped blit")
var b = SoftwareBackend.create()
if b.init(4, 4):
    b.clear(BG)
    b.set_clip(1, 1, 1, 2)
    b.draw_image(1, 0, 1, 4, [
        0xFFFF0000u32, 0xFF00FF00u32,
        0xFF0000FFu32, 0xFFFFFF00u32
    ])
    val p = b.read_pixels()
    expect(p[0 * 4 + 1]).to_equal(BG)
    expect(p[1 * 4 + 1]).to_equal(0xFF00FF00u32)
    expect(p[2 * 4 + 1]).to_equal(0xFF0000FFu32)
    expect(p[3 * 4 + 1]).to_equal(BG)
    b.shutdown()
```

</details>

#### draw_rect_filled fills its interior

- draw_rect_filled fills its interior
   - Expected: p[4 * 32 + 4] equals `0xFFFF0000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rect_filled fills its interior")
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_rect_filled(2, 2, 10, 10, 0xFFFF0000u32)
    val p = b.read_pixels()
    expect(p[4 * 32 + 4]).to_equal(0xFFFF0000u32)
    b.shutdown()
```

</details>

#### draw_rect_filled respects active clip bounds

- draw_rect_filled respects active clip bounds
   - Expected: p[3 * 32 + 3] equals `0xFFFF0000u32`
   - Expected: p[5 * 32 + 5] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rect_filled respects active clip bounds")
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.set_clip(0, 0, 4, 4)
    b.draw_rect_filled(2, 2, 8, 8, 0xFFFF0000u32)
    val p = b.read_pixels()
    expect(p[3 * 32 + 3]).to_equal(0xFFFF0000u32)
    expect(p[5 * 32 + 5]).to_equal(BG)
    b.shutdown()
```

</details>

#### draw_circle_filled writes its center (regression)

- draw_circle_filled writes its center (regression)
   - Expected: p[16 * 32 + 16] equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_circle_filled writes its center (regression)")
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_circle_filled(16, 16, 8, 0xFF00FF00u32)
    val p = b.read_pixels()
    expect(p[16 * 32 + 16]).to_equal(0xFF00FF00u32)
    b.shutdown()
```

</details>

#### draw_line writes pixels along the line (regression)

- draw_line writes pixels along the line (regression)
   - Expected: p[16 * 32 + 15] equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_line writes pixels along the line (regression)")
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_line(1, 16, 30, 16, 0xFF0000FFu32, 3)
    val p = b.read_pixels()
    expect(p[16 * 32 + 15]).to_equal(0xFF0000FFu32)
    b.shutdown()
```

</details>

#### draw_gradient_rect shades top-to-bottom (regression)

- draw_gradient_rect shades top-to-bottom (regression)
   - Expected: top != BG is true
   - Expected: bot != BG is true
   - Expected: top != bot is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_gradient_rect shades top-to-bottom (regression)")
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_gradient_rect(1, 1, 12, 28, 0xFFFF0000u32, 0xFF0000FFu32)
    val p = b.read_pixels()
    val top = p[2 * 32 + 6]
    val bot = p[26 * 32 + 6]
    expect(top != BG).to_equal(true)
    expect(bot != BG).to_equal(true)
    expect(top != bot).to_equal(true)
    b.shutdown()
```

</details>

#### draw_rounded_rect draws edge and rounds the corner (regression)

- draw_rounded_rect draws edge and rounds the corner (regression)
   - Expected: p[4 * 32 + 16] equals `0xFFFFFF00u32`
   - Expected: p[4 * 32 + 4] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rounded_rect draws edge and rounds the corner (regression)")
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_rounded_rect(4, 4, 24, 24, 5, 0xFFFFFF00u32)
    val p = b.read_pixels()
    expect(p[4 * 32 + 16]).to_equal(0xFFFFFF00u32)
    expect(p[4 * 32 + 4]).to_equal(BG)
    b.shutdown()
```

</details>

#### draw_text writes glyph pixels (regression)

- draw_text writes glyph pixels (regression)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_text writes glyph pixels (regression)")
var b = SoftwareBackend.create()
if b.init(48, 16):
    b.clear(BG)
    b.draw_text(1, 2, "Hi", 0xFFFFFFFFu32, 8)
    val p = b.read_pixels()
    var n = 0
    var i = 0
    val pixel_count = p.len()
    while i < pixel_count:
        if p[i] != BG:
            n = n + 1
        i = i + 1
    expect(n).to_be_greater_than(0)
    b.shutdown()
```

</details>

#### draw_text clips offscreen spans on the fast path

- draw_text clips offscreen spans on the fast path


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_text clips offscreen spans on the fast path")
var full = SoftwareBackend.create()
var left = SoftwareBackend.create()
var right = SoftwareBackend.create()
if full.init(48, 16) and left.init(48, 16) and right.init(48, 16):
    full.clear(BG)
    left.clear(BG)
    right.clear(BG)
    full.draw_text(8, 2, "Hi", 0xFFFFFFFFu32, 8)
    left.draw_text(-4, 2, "Hi", 0xFFFFFFFFu32, 8)
    right.draw_text(44, 2, "Hi", 0xFFFFFFFFu32, 8)
    val full_p = full.read_pixels()
    val left_p = left.read_pixels()
    val right_p = right.read_pixels()
    var full_count = 0
    var left_count = 0
    var right_count = 0
    var i = 0
    val pixel_count = full_p.len()
    while i < pixel_count:
        if full_p[i] != BG:
            full_count = full_count + 1
        if left_p[i] != BG:
            left_count = left_count + 1
        if right_p[i] != BG:
            right_count = right_count + 1
        i = i + 1
    expect(left_count).to_be_greater_than(0)
    expect(right_count).to_be_greater_than(0)
    expect(left_count).to_be_less_than(full_count)
    expect(right_count).to_be_less_than(full_count)
    full.shutdown()
    left.shutdown()
    right.shutdown()
```

</details>

#### draw_text respects active clip bounds

- draw_text respects active clip bounds
   - Expected: n equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_text respects active clip bounds")
var b = SoftwareBackend.create()
if b.init(48, 16):
    b.clear(BG)
    b.set_clip(32, 0, 8, 16)
    b.draw_text(1, 2, "Hi", 0xFFFFFFFFu32, 8)
    val p = b.read_pixels()
    var n = 0
    var i = 0
    val pixel_count = p.len()
    while i < pixel_count:
        if p[i] != BG:
            n = n + 1
        i = i + 1
    expect(n).to_equal(0)
    b.shutdown()
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `117f467e197e9b225a54209f87d3a6db5ddce3c6148c104cae7ad193c4715e0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `117f467e197e9b225a54209f87d3a6db5ddce3c6148c104cae7ad193c4715e0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `117f467e197e9b225a54209f87d3a6db5ddce3c6148c104cae7ad193c4715e0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_image preserves each source row in a one-column clipped blit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled fills its interior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled respects active clip bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
