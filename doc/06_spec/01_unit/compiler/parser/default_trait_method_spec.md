# Default trait methods spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default trait methods spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/default_trait_method_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### default trait methods

#### trait with only defaults parses and resolves

- trait with only defaults parses and resolves
   - Expected: result equals `Good day, sir.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("trait with only defaults parses and resolves")
# Greetable has only default methods -- no required ones
val result = greet_formal_default()
expect(result).to_equal("Good day, sir.")
```

</details>

#### default methods are inherited when not overridden

- default methods are inherited when not overridden
   - Expected: result equals `Hey!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default methods are inherited when not overridden")
val result = greet_casual_default()
expect(result).to_equal("Hey!")
```

</details>

#### required method can be implemented

- required method can be implemented
   - Expected: result equals `FormalPerson(Alice)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("required method can be implemented")
val result = formal_person_to_string()
expect(result).to_equal("FormalPerson(Alice)")
```

</details>

#### default method can be overridden in impl

- default method can be overridden in impl
   - Expected: result equals `Yo, what's up!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default method can be overridden in impl")
val result = casual_greet()
expect(result).to_equal("Yo, what's up!")
```

</details>

### trait definition structure
_Structural checks that avoid placeholder assertions._

#### trait with mixed required and default methods parses

- trait with mixed required and default methods parses
   - Expected: printable_default_method_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("trait with mixed required and default methods parses")
expect(printable_default_method_count()).to_equal(2)
expect(formal_person_to_string()).to_contain("Alice")
```

</details>

#### all-default trait behavior is available without dummy impl bodies

- all-default trait behavior is available without dummy impl bodies
   - Expected: greetable_required_method_count() equals `0`
   - Expected: greet_formal_default() equals `Good day, sir.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("all-default trait behavior is available without dummy impl bodies")
expect(greetable_required_method_count()).to_equal(0)
expect(greet_formal_default()).to_equal("Good day, sir.")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca89bd572ad6c990c92e8e1bb8b958f3a2222291604b0272a25e739086bfded6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca89bd572ad6c990c92e8e1bb8b958f3a2222291604b0272a25e739086bfded6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca89bd572ad6c990c92e8e1bb8b958f3a2222291604b0272a25e739086bfded6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/parser/default_trait_method_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/default_trait_method_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/default_trait_method_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/default_trait_method_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/default_trait_method_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/default_trait_method_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trait with only defaults parses and resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/default_trait_method_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default methods are inherited when not overridden' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/default_trait_method_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'required method can be implemented' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
