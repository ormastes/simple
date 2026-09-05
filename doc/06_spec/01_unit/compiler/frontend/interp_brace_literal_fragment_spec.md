# Interp Brace Literal Fragment Specification

> Tests covering interpolation fragment brace-literal rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Brace Literal Fragment Specification

## Scenarios

### interpolation fragment brace-literal rejection

#### rejects a region whose whole content is a brace literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a region whose whole content is a brace literal
   - Expected: module.functions contains `warm`
   - Expected: parse_interpolation_fragment(" " + brace("inner") + " ") equals `-1`
   - Expected: parse_interpolation_fragment(" " + brace("inner")) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a region whose whole content is a brace literal")
# Warm the lexer/parser globals the fragment parser reuses.
val module = parse_and_build_module("fn warm() -> i64:\n    1\n", "warm.spl")
expect(module.functions.contains("warm")).to_equal(true)

# Exact shapes from the bug report: "{ {inner} }" and "{ {inner}}".
expect(parse_interpolation_fragment(" " + brace("inner") + " ")).to_equal(-1)
expect(parse_interpolation_fragment(" " + brace("inner"))).to_equal(-1)
```

</details>

#### rejects the wider brace-literal class, padded or not

- rejects the wider brace-literal class, padded or not
   - Expected: module.functions contains `warm2`
   - Expected: parse_interpolation_fragment(brace("inner")) equals `-1`
   - Expected: parse_interpolation_fragment(brace("a: 1")) equals `-1`
   - Expected: parse_interpolation_fragment("  " + brace("1, 2") + "  ") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects the wider brace-literal class, padded or not")
# Generalises past the two reported shapes: any padding, any inner
# syntax. A dict-shaped or set-shaped region is literal text, never an
# interpolation.
val module = parse_and_build_module("fn warm2() -> i64:\n    1\n", "warm2.spl")
expect(module.functions.contains("warm2")).to_equal(true)

expect(parse_interpolation_fragment(brace("inner"))).to_equal(-1)
expect(parse_interpolation_fragment(brace("a: 1"))).to_equal(-1)
expect(parse_interpolation_fragment("  " + brace("1, 2") + "  ")).to_equal(-1)
```

</details>

#### still accepts ordinary interpolation fragments

- still accepts ordinary interpolation fragments
   - Expected: module.functions contains `warm3`
   - Expected: parse_interpolation_fragment("inner") >= 0 is true
   - Expected: parse_interpolation_fragment(" a + b ") >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still accepts ordinary interpolation fragments")
val module = parse_and_build_module("fn warm3() -> i64:\n    1\n", "warm3.spl")
expect(module.functions.contains("warm3")).to_equal(true)

expect(parse_interpolation_fragment("inner") >= 0).to_equal(true)
expect(parse_interpolation_fragment(" a + b ") >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpolation fragment brace-literal rejection.
- interpolation fragment brace-literal rejection

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea7fe7bc78224b3ce62f0000ef847f7f531bac4f4be6cd6bbefe0e48b7de74a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea7fe7bc78224b3ce62f0000ef847f7f531bac4f4be6cd6bbefe0e48b7de74a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea7fe7bc78224b3ce62f0000ef847f7f531bac4f4be6cd6bbefe0e48b7de74a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a region whose whole content is a brace literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the wider brace-literal class, padded or not' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts ordinary interpolation fragments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
