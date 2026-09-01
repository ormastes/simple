# Pure Simple Interpolation Literal Segments Specification

> Tests covering pure-Simple interpreter interpolated-string literal segments.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Simple Interpolation Literal Segments Specification

## Scenarios

### pure-Simple interpreter interpolated-string literal segments

#### keeps the literal prefix and separator of a numeric diagnostic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the literal prefix and separator of a numeric diagnostic
   - Expected: render(src, names, ints) equals `heap_registry=807339 phase=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the literal prefix and separator of a numeric diagnostic")
# print("heap_registry={n} phase={p}")
val src = prog(
    "\"heap_registry=" + lb() + "n" + rb() +
    " phase=" + lb() + "p" + rb() + "\""
)
val names: [text] = ["n", "p"]
val ints: [i64] = [807339, 2]
# RED shape when the drifted copy wins: "8073392" — literals dropped.
expect(render(src, names, ints)).to_equal("heap_registry=807339 phase=2")
```

</details>

#### keeps leading, interior and trailing literal text in every position

- keeps leading, interior and trailing literal text in every position
   - Expected: render(leading, nm, iv) equals `pre=7`
   - Expected: render(trailing, nm, iv) equals `7=post`
   - Expected: render(both, nm, iv) equals `[7]`
   - Expected: render(interior, nm2, iv2) equals `7 to 9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps leading, interior and trailing literal text in every position")
val leading = prog("\"pre=" + lb() + "a" + rb() + "\"")
val nm: [text] = ["a"]
val iv: [i64] = [7]
expect(render(leading, nm, iv)).to_equal("pre=7")

val trailing = prog("\"" + lb() + "a" + rb() + "=post\"")
expect(render(trailing, nm, iv)).to_equal("7=post")

val both = prog("\"[" + lb() + "a" + rb() + "]\"")
expect(render(both, nm, iv)).to_equal("[7]")

val nm2: [text] = ["a", "b"]
val iv2: [i64] = [7, 9]
val interior = prog(
    "\"" + lb() + "a" + rb() + " to " + lb() + "b" + rb() + "\""
)
expect(render(interior, nm2, iv2)).to_equal("7 to 9")
```

</details>

#### decodes doubled brace escapes in the literal segments

- decodes doubled brace escapes in the literal segments
   - Expected: render(src, nm, iv) equals `lb() + "literal" + rb() + " 7"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes doubled brace escapes in the literal segments")
# print("{{literal}} {a}") must render "{literal} 7"
val src = prog(
    "\"" + lb() + lb() + "literal" + rb() + rb() +
    " " + lb() + "a" + rb() + "\""
)
val nm: [text] = ["a"]
val iv: [i64] = [7]
expect(render(src, nm, iv)).to_equal(lb() + "literal" + rb() + " 7")
```

</details>

#### renders an expression region alongside its literal text

- renders an expression region alongside its literal text
   - Expected: render(src, nm, iv) equals `sum=5!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an expression region alongside its literal text")
val src = prog("\"sum=" + lb() + "a + b" + rb() + "!\"")
val nm: [text] = ["a", "b"]
val iv: [i64] = [2, 3]
expect(render(src, nm, iv)).to_equal("sum=5!")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple interpreter interpolated-string literal segments.
- pure-Simple interpreter interpolated-string literal segments

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

- Canonical SPipe generation for source `e1adbddc009e3246081595d6c09d0598e259cf244230327062e73448e6e5c05f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1adbddc009e3246081595d6c09d0598e259cf244230327062e73448e6e5c05f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1adbddc009e3246081595d6c09d0598e259cf244230327062e73448e6e5c05f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the literal prefix and separator of a numeric diagnostic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps leading, interior and trailing literal text in every position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes doubled brace escapes in the literal segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
