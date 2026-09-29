# Text Advanced Case Class Generalization Specification

> Tests covering case-conversion char-arithmetic defect class (adjacent ops).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Advanced Case Class Generalization Specification

## Scenarios

### case-conversion char-arithmetic defect class (adjacent ops)

#### kebab-cases PascalCase without leaking numeric char codes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- kebab-cases PascalCase without leaking numeric char codes
   - Expected: to_kebab_case("HelloWorld") equals `hello-world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kebab-cases PascalCase without leaking numeric char codes")
expect(to_kebab_case("HelloWorld")).to_equal("hello-world")
```

</details>

#### pascal-cases snake_case without leaking numeric char codes

- pascal-cases snake_case without leaking numeric char codes
   - Expected: to_pascal_case("hello_world") equals `HelloWorld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pascal-cases snake_case without leaking numeric char codes")
expect(to_pascal_case("hello_world")).to_equal("HelloWorld")
```

</details>

#### screaming-snakes camelCase without leaking numeric char codes

- screaming-snakes camelCase without leaking numeric char codes
   - Expected: to_screaming_snake("helloWorld") equals `HELLO_WORLD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("screaming-snakes camelCase without leaking numeric char codes")
expect(to_screaming_snake("helloWorld")).to_equal("HELLO_WORLD")
```

</details>

#### round-trips snake -> camel -> snake losslessly

- round-trips snake -> camel -> snake losslessly
   - Expected: to_snake_case(to_camel_case("alpha_beta_gamma")) equals `alpha_beta_gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips snake -> camel -> snake losslessly")
expect(to_snake_case(to_camel_case("alpha_beta_gamma"))).to_equal("alpha_beta_gamma")
```

</details>

#### flips every letter of a fully-uppercase word

- flips every letter of a fully-uppercase word
   - Expected: to_snake_case("ABC") equals `a_b_c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flips every letter of a fully-uppercase word")
# A single surviving `ch[0] + 32` produces "A32..." here, never "abc".
expect(to_snake_case("ABC")).to_equal("a_b_c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/text_advanced_case_class_generalization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering case-conversion char-arithmetic defect class (adjacent ops).
- case-conversion char-arithmetic defect class (adjacent ops)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9c104f6c4e8a7929da68f7b009e87b7867e35cce4fe66a041a1645028e44ac98`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c104f6c4e8a7929da68f7b009e87b7867e35cce4fe66a041a1645028e44ac98`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c104f6c4e8a7929da68f7b009e87b7867e35cce4fe66a041a1645028e44ac98`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/text_advanced_case_class_generalization_spec.spl
mirror: doc/06_spec/unit/lib/common/text_advanced_case_class_generalization_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/text_advanced_case_class_generalization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/text_advanced_case_class_generalization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/text_advanced_case_class_generalization_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kebab-cases PascalCase without leaking numeric char codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/text_advanced_case_class_generalization_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pascal-cases snake_case without leaking numeric char codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/text_advanced_case_class_generalization_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'screaming-snakes camelCase without leaking numeric char codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
