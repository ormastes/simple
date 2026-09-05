# String Interpolation Specification

> Tests covering self-hosted interpreter string interpolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Interpolation Specification

## Scenarios

### self-hosted interpreter string interpolation

#### evaluates variables expressions and multiple regions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evaluates variables expressions and multiple regions
   - Expected: "bare={a}" equals `bare=2`
   - Expected: "expr={a + b}" equals `expr=5`
   - Expected: "nested {a} and {b}" equals `nested 2 and 3`
   - Expected: "joined={words.join("-")}" equals `joined=a-b`
   - Expected: "{{literal}} {a}" equals `{literal} 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("evaluates variables expressions and multiple regions")
val a = 2
val b = 3
val words = ["a", "b"]

expect("bare={a}").to_equal("bare=2")
expect("expr={a + b}").to_equal("expr=5")
expect("nested {a} and {b}").to_equal("nested 2 and 3")
expect("joined={words.join("-")}").to_equal("joined=a-b")
expect("{{literal}} {a}").to_equal("{literal} 2")
```

</details>

#### keeps escaped and non-expression braces literal

- keeps escaped and non-expression braces literal
   - Expected: escaped equals `{" + "not interpolation" + "}`
   - Expected: css equals `{" + " color: red; " + "}`
   - Expected: after equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps escaped and non-expression braces literal")
val escaped = "{{not interpolation}}"
val css = "{ color: red; }"
val mixed_invalid = "before {value} then { color: red; }"
val after = 9

expect(escaped).to_equal("{" + "not interpolation" + "}")
expect(css).to_equal("{" + " color: red; " + "}")
expect(mixed_invalid).to_equal(
    "before " + "{value}" + " then " + "{ color: red; }"
)
expect(after).to_equal(9)
```

</details>

#### does not interpolate raw strings

- does not interpolate raw strings
   - Expected: raw equals `{" + "value" + "}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not interpolate raw strings")
val value = 7
val raw = r"{value}"

expect(raw).to_equal("{" + "value" + "}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/string_interpolation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering self-hosted interpreter string interpolation.
- self-hosted interpreter string interpolation

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

- Canonical SPipe generation for source `8afe74e16e03df26e1f0b7f63dc61eb5bb05fb1f25e930ec40caa8d28b98a18a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8afe74e16e03df26e1f0b7f63dc61eb5bb05fb1f25e930ec40caa8d28b98a18a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8afe74e16e03df26e1f0b7f63dc61eb5bb05fb1f25e930ec40caa8d28b98a18a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/interpreter/string_interpolation_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/string_interpolation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/string_interpolation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/string_interpolation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/string_interpolation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/string_interpolation_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates variables expressions and multiple regions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/string_interpolation_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps escaped and non-expression braces literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/string_interpolation_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not interpolate raw strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
