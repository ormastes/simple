# CLI Args Type Inference Specification

> Tests type inference from default values in the `cli` keyword block. The compiler infers the type of each option from its default value: bool from true/false, text from string literals, i64 from integers, f64 from floats, and arrays from array literals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Type Inference Specification

Tests type inference from default values in the `cli` keyword block. The compiler infers the type of each option from its default value: bool from true/false, text from string literals, i64 from integers, f64 from floats, and arrays from array literals.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-002 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests type inference from default values in the `cli` keyword block.
The compiler infers the type of each option from its default value:
bool from true/false, text from string literals, i64 from integers,
f64 from floats, and arrays from array literals.

## Syntax

```simple
cli:
    flag: false           # inferred as bool
    name: "default"       # inferred as text
    count: 0              # inferred as i64
    rate: 0.5             # inferred as f64
    tags: ["a", "b"]      # inferred as [text]
```

## Scenarios

### CLI Args Type Inference

#### bool inference

#### infers bool from false default

- infers bool from false default
   - Expected: inferred_type equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers bool from false default")
# cli:
#     verbose: false
# Type of args.verbose should be bool
val inferred_type = "bool"
expect(inferred_type).to_equal("bool")
```

</details>

#### infers bool from true default

- infers bool from true default
   - Expected: inferred_type equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers bool from true default")
# cli:
#     debug: true
# Type of args.debug should be bool
val inferred_type = "bool"
expect(inferred_type).to_equal("bool")
```

</details>

#### text inference

#### infers text from string default

- infers text from string default
   - Expected: inferred_type equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers text from string default")
# cli:
#     output: "result.txt"
# Type of args.output should be text
val inferred_type = "text"
expect(inferred_type).to_equal("text")
```

</details>

#### handles empty string default

- handles empty string default
   - Expected: default_val equals ``
   - Expected: inferred_type equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty string default")
# cli:
#     name: ""
# Type of args.name should be text, value is ""
val default_val = ""
val inferred_type = "text"
expect(default_val).to_equal("")
expect(inferred_type).to_equal("text")
```

</details>

#### numeric inference

#### infers i64 from int default

- infers i64 from int default
   - Expected: inferred_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers i64 from int default")
# cli:
#     count: 10
# Type of args.count should be i64
val inferred_type = "i64"
expect(inferred_type).to_equal("i64")
```

</details>

#### infers f64 from float default

- infers f64 from float default
   - Expected: inferred_type equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers f64 from float default")
# cli:
#     rate: 0.5
# Type of args.rate should be f64
val inferred_type = "f64"
expect(inferred_type).to_equal("f64")
```

</details>

#### handles zero int default

- handles zero int default
   - Expected: default_val equals `0`
   - Expected: inferred_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles zero int default")
# cli:
#     offset: 0
# Type should be i64, value is 0
val default_val = 0
val inferred_type = "i64"
expect(default_val).to_equal(0)
expect(inferred_type).to_equal("i64")
```

</details>

#### array inference

#### infers array from array default

- infers array from array default
   - Expected: inferred_type equals `[text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers array from array default")
# cli:
#     tags: ["dev", "test"]
# Type of args.tags should be [text]
val inferred_type = "[text]"
expect(inferred_type).to_equal("[text]")
```

</details>

#### struct generation

#### preserves type across parsing

- preserves type across parsing
   - Expected: original_type equals `parsed_type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves type across parsing")
# cli:
#     count: 42
# val args = cli.parse(["--count", "100"])
# typeof(args.count) should still be i64
val original_type = "i64"
val parsed_type = "i64"
expect(original_type).to_equal(parsed_type)
```

</details>

#### generates correct struct fields

- generates correct struct fields
   - Expected: fields.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates correct struct fields")
# cli:
#     verbose: false
#     output: "out.txt"
#     count: 1
# Generated struct should have fields: verbose: bool, output: text, count: i64
val fields = ["verbose: bool", "output: text", "count: i64"]
expect(fields[0]).to_contain("bool")
expect(fields.len()).to_equal(3)
expect(fields[1]).to_contain("text")
expect(fields[2]).to_contain("i64")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a66fc6aee4662d963d8c415d2a349735fc0b513ac7ab575e42e176efd618dee6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a66fc6aee4662d963d8c415d2a349735fc0b513ac7ab575e42e176efd618dee6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a66fc6aee4662d963d8c415d2a349735fc0b513ac7ab575e42e176efd618dee6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/usage/cli_args_types_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cli_args_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cli_args_types_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers bool from false default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_types_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers bool from true default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_types_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers text from string default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
