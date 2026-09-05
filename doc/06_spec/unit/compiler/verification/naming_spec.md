# Naming Specification

> Tests covering Lean Naming Conventions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Naming Specification

## Scenarios

### Lean Naming Conventions

#### PascalCase

#### converts snake case

- converts snake case
   - Expected: naming.to_pascal_case("ref_capability") equals `RefCapability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts snake case")
expect(naming.to_pascal_case("ref_capability")).to_equal("RefCapability")
```

</details>

#### handles empty input

- handles empty input
   - Expected: naming.to_pascal_case("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty input")
expect(naming.to_pascal_case("")).to_equal("")
```

</details>

#### camelCase

#### converts snake case

- converts snake case
   - Expected: naming.to_camel_case("get_value") equals `getValue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts snake case")
expect(naming.to_camel_case("get_value")).to_equal("getValue")
```

</details>

#### lowercases the first character

- lowercases the first character
   - Expected: naming.to_camel_case("UPPER") equals `uPPER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowercases the first character")
expect(naming.to_camel_case("UPPER")).to_equal("uPPER")
```

</details>

#### reserved words

#### detects Lean keywords

- detects Lean keywords
   - Expected: naming.is_reserved("let") is true
   - Expected: naming.is_reserved("forall") is true
   - Expected: naming.is_reserved("myFunction") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects Lean keywords")
expect(naming.is_reserved("let")).to_equal(true)
expect(naming.is_reserved("forall")).to_equal(true)
expect(naming.is_reserved("myFunction")).to_equal(false)
```

</details>

#### escapes reserved identifiers

- escapes reserved identifiers
   - Expected: naming.sanitize_lean_ident("def") equals `«def»`
   - Expected: naming.sanitize_lean_ident("myVar") equals `myVar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes reserved identifiers")
expect(naming.sanitize_lean_ident("def")).to_equal("«def»")
expect(naming.sanitize_lean_ident("myVar")).to_equal("myVar")
```

</details>

#### Lean name helpers

#### converts type names

- converts type names
   - Expected: naming.to_lean_type_name("my_type") equals `MyType`
   - Expected: naming.to_lean_type_name("type") equals `«Type»`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts type names")
expect(naming.to_lean_type_name("my_type")).to_equal("MyType")
expect(naming.to_lean_type_name("type")).to_equal("«Type»")
```

</details>

#### converts function names

- converts function names
   - Expected: naming.to_lean_func_name("my_function") equals `myFunction`
   - Expected: naming.to_lean_func_name("let") equals `«let»`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts function names")
expect(naming.to_lean_func_name("my_function")).to_equal("myFunction")
expect(naming.to_lean_func_name("let")).to_equal("«let»")
```

</details>

#### converts namespaces and identifiers

- converts namespaces and identifiers
   - Expected: naming.to_lean_namespace("std.collections") equals `Std.Collections`
   - Expected: naming.to_lean_ident("my-var") equals `my_var`
   - Expected: naming.to_lean_ident("123abc") equals `_123abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts namespaces and identifiers")
expect(naming.to_lean_namespace("std.collections")).to_equal("Std.Collections")
expect(naming.to_lean_ident("my-var")).to_equal("my_var")
expect(naming.to_lean_ident("123abc")).to_equal("_123abc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/verification/naming_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean Naming Conventions.
- Lean Naming Conventions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `b3fe4f32659c6ff5a52dfde4d5401490c25f7616119e146acbb7d04bee46a347`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3fe4f32659c6ff5a52dfde4d5401490c25f7616119e146acbb7d04bee46a347`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3fe4f32659c6ff5a52dfde4d5401490c25f7616119e146acbb7d04bee46a347`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/verification/naming_spec.spl
mirror: doc/06_spec/unit/compiler/verification/naming_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verification/naming_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verification/naming_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verification/naming_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts snake case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/naming_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/naming_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts snake case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
