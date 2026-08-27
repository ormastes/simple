# Glyph Specification

> Tests covering Engine2D glyph data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glyph Specification

## Scenarios

### Engine2D glyph data

#### returns shared uppercase glyph rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns shared uppercase glyph rows
   - Expected: glyph_data("A") equals `[0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001]`
   - Expected: glyph_data("Z") equals `[0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns shared uppercase glyph rows")
expect(glyph_data("A")).to_equal([0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001])
expect(glyph_data("Z")).to_equal([0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111])
```

</details>

#### returns shared lowercase glyph rows

- returns shared lowercase glyph rows
   - Expected: glyph_data("a") equals `[0b00000, 0b01110, 0b00001, 0b01111, 0b10001, 0b01111, 0b00000]`
   - Expected: glyph_data("z") equals `[0b00000, 0b11111, 0b00010, 0b00100, 0b01000, 0b11111, 0b00000]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns shared lowercase glyph rows")
expect(glyph_data("a")).to_equal([0b00000, 0b01110, 0b00001, 0b01111, 0b10001, 0b01111, 0b00000])
expect(glyph_data("z")).to_equal([0b00000, 0b11111, 0b00010, 0b00100, 0b01000, 0b11111, 0b00000])
```

</details>

#### returns shared digit glyph rows

- returns shared digit glyph rows
   - Expected: glyph_data("0") equals `[0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110]`
   - Expected: glyph_data("9") equals `[0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00010, 0b01100]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns shared digit glyph rows")
expect(glyph_data("0")).to_equal([0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110])
expect(glyph_data("9")).to_equal([0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00010, 0b01100])
```

</details>

#### returns shared punctuation rows and box-outline unknown fallback

- returns shared punctuation rows and box-outline unknown fallback
   - Expected: glyph_data(" ") equals `[0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000]`
   - Expected: glyph_data("?") equals `[0b01110, 0b10001, 0b00010, 0b00100, 0b00100, 0b00000, 0b00100]`
   - Expected: glyph_data("\"") equals `[0b01010, 0b01010, 0b01010, 0b00000, 0b00000, 0b00000, 0b00000]`
   - Expected: glyph_data("\\") equals `[0b10000, 0b01000, 0b01000, 0b00100, 0b00010, 0b00010, 0b00001]`
   - Expected: glyph_data("|") equals `[0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111]`
   - Expected: glyph_data("~") equals `[0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111]`
   - Expected: glyph_data("") equals `[0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111]`
   - Expected: glyph_data("\n") equals `[0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111]`
   - Expected: glyph_data("AA") equals `[0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns shared punctuation rows and box-outline unknown fallback")
expect(glyph_data(" ")).to_equal([0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000])
expect(glyph_data("?")).to_equal([0b01110, 0b10001, 0b00010, 0b00100, 0b00100, 0b00000, 0b00100])
expect(glyph_data("\"")).to_equal([0b01010, 0b01010, 0b01010, 0b00000, 0b00000, 0b00000, 0b00000])
expect(glyph_data("\\")).to_equal([0b10000, 0b01000, 0b01000, 0b00100, 0b00010, 0b00010, 0b00001])
# '|' and '~' are outside the shared 88-char charset -> unknown box outline
expect(glyph_data("|")).to_equal([0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111])
expect(glyph_data("~")).to_equal([0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111])
expect(glyph_data("")).to_equal([0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111])
expect(glyph_data("\n")).to_equal([0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111])
expect(glyph_data("AA")).to_equal([0b11111, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11111])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/glyph_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D glyph data.
- Engine2D glyph data

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `d575a7b9da7223b08b13aaef505374ded142f07e6c6ca4f3b785210b4cd8dd85`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d575a7b9da7223b08b13aaef505374ded142f07e6c6ca4f3b785210b4cd8dd85`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d575a7b9da7223b08b13aaef505374ded142f07e6c6ca4f3b785210b4cd8dd85`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/glyph_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/glyph_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/glyph_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/glyph_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/glyph_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns shared uppercase glyph rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/glyph_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns shared lowercase glyph rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/glyph_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns shared digit glyph rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
