# backend_software_primitives_spec

> Software Backend Primitive Rendering Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_software_primitives_spec

Software Backend Primitive Rendering Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl` |
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

#### draw_rect_filled fills its interior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- draw_rect_filled fills its interior
   - Expected: p[4 * 32 + 4] equals `0xFFFF0000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
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

#### draw_circle_filled writes its center (regression)

- draw_circle_filled writes its center (regression)
   - Expected: p[16 * 32 + 16] equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_text writes glyph pixels (regression)")
var b = SoftwareBackend.create()
if b.init(48, 16):
    b.clear(BG)
    b.draw_text(1, 2, "Hi", 0xFFFFFFFFu32, 8)
    val p = b.read_pixels()
    var n = 0
    var i = 0
    while i < p.len():
        if p[i] != BG:
            n = n + 1
        i = i + 1
    expect(n).to_be_greater_than(0)
    b.shutdown()
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

- Canonical SPipe generation for source `85bd38c21ff1873a345fe5936a78043db9411cdf2ce9211365afefd65dbec49a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85bd38c21ff1873a345fe5936a78043db9411cdf2ce9211365afefd65dbec49a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85bd38c21ff1873a345fe5936a78043db9411cdf2ce9211365afefd65dbec49a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl
mirror: doc/06_spec/unit/lib/gpu/engine2d/backend_software_primitives_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gpu/engine2d/backend_software_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gpu/engine2d/backend_software_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled fills its interior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_circle_filled writes its center (regression)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_line writes pixels along the line (regression)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
