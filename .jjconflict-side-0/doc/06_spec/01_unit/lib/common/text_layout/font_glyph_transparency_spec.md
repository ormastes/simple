# Font Glyph Transparency Specification

> Tests covering font glyph transparency / alpha compositing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Glyph Transparency Specification

## Scenarios

### font glyph transparency / alpha compositing

#### full coverage replaces the background with the foreground

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- full coverage replaces the background with the foreground
   - Expected: _r(out[0]) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("full coverage replaces the background with the foreground")
var buf: [u32] = [_argb(255, 0, 0, 0)]
val out = blit_glyph(buf, 1, 1, 0, 0, _glyph_1x1(255), _argb(255, 255, 255, 255))
expect(_r(out[0])).to_equal(255)
```

</details>

#### half coverage blends toward the foreground (midpoint)

- half coverage blends toward the foreground (midpoint)
   - Expected: _r(out[0]) equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("half coverage blends toward the foreground (midpoint)")
var buf: [u32] = [_argb(255, 0, 0, 0)]
val out = blit_glyph(buf, 1, 1, 0, 0, _glyph_1x1(128), _argb(255, 255, 255, 255))
# (255*128 + 0*127)/255 == 128
expect(_r(out[0])).to_equal(128)
```

</details>

#### zero coverage leaves the background unchanged

- zero coverage leaves the background unchanged
   - Expected: _r(out[0]) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("zero coverage leaves the background unchanged")
var buf: [u32] = [_argb(255, 10, 20, 30)]
val out = blit_glyph(buf, 1, 1, 0, 0, _glyph_1x1(0), _argb(255, 255, 255, 255))
expect(_r(out[0])).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering font glyph transparency / alpha compositing.
- font glyph transparency / alpha compositing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `b057bf14f90d569e031b73e1ceeca7f9453c91fb19d4c029732697d56e41d867`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b057bf14f90d569e031b73e1ceeca7f9453c91fb19d4c029732697d56e41d867`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b057bf14f90d569e031b73e1ceeca7f9453c91fb19d4c029732697d56e41d867`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_layout/font_glyph_transparency_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_layout/font_glyph_transparency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_layout/font_glyph_transparency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'full coverage replaces the background with the foreground' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'half coverage blends toward the foreground (midpoint)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero coverage leaves the background unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
