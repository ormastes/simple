# Lean Basic Specification

> Tests covering Lean Basic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Basic Specification

## Scenarios

### Lean Basic

#### LeanEmitter

#### emits indented lines

- emits indented lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits indented lines")
var emit = emitter.LeanEmitter.new()
emit.emit_line("structure Foo where")
emit.indent()
emit.emit_line("x : Int")
emit.emit_line("y : Bool")
emit.dedent()

val output = emit.finish()
expect(output).to_contain("structure Foo where")
expect(output).to_contain("  x : Int")
expect(output).to_contain("  y : Bool")
```

</details>

#### renders structure and theorem helpers

- renders structure and theorem helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders structure and theorem helpers")
var emit = emitter.LeanEmitter.new()
emit.emit_structure_data("Point", [("x", "Int"), ("y", "Int")], ["Repr"])
emit.emit_theorem_data("point_eq", [("x", "Int")], "x = x", Some("rfl"), false)

val output = emit.finish()
expect(output).to_contain("structure Point where")
expect(output).to_contain("deriving Repr")
expect(output).to_contain("theorem point_eq")
expect(output).to_contain("rfl")
```

</details>

#### fails closed for a missing theorem proof when sorry is disabled

- fails closed for a missing theorem proof when sorry is disabled
   - Expected: output does not contain `sorry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for a missing theorem proof when sorry is disabled")
var emit = emitter.LeanEmitter.new()
emit.emit_theorem_data("missing_proof", [], "True", nil, false)
val output = emit.finish()
expect(output).to_contain("FV2-E-LEAN-PROOF-MISSING")
expect(output.contains("sorry")).to_equal(false)
```

</details>

#### Naming conventions

#### translates module and identifier names

- translates module and identifier names
   - Expected: naming.to_pascal_case("my_type") equals `MyType`
   - Expected: naming.to_camel_case("get_value") equals `getValue`
   - Expected: naming.to_lean_namespace("std.collections") equals `Std.Collections`
   - Expected: naming.to_lean_ident("my var") equals `my_var`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates module and identifier names")
expect(naming.to_pascal_case("my_type")).to_equal("MyType")
expect(naming.to_camel_case("get_value")).to_equal("getValue")
expect(naming.to_lean_namespace("std.collections")).to_equal("Std.Collections")
expect(naming.to_lean_ident("my var")).to_equal("my_var")
```

</details>

#### detects and escapes reserved words

- detects and escapes reserved words
   - Expected: naming.is_reserved("let") is true
   - Expected: naming.is_reserved("myVar") is false
   - Expected: naming.sanitize_lean_ident("def") equals `«def»`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects and escapes reserved words")
expect(naming.is_reserved("let")).to_equal(true)
expect(naming.is_reserved("myVar")).to_equal(false)
expect(naming.sanitize_lean_ident("def")).to_equal("«def»")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/lean_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean Basic.
- Lean Basic

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

- Canonical SPipe generation for source `eeff3d5d8b4e6c3a5c831f4d5df564beb30b618851e72ae2b2ce40f86a1752b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeff3d5d8b4e6c3a5c831f4d5df564beb30b618851e72ae2b2ce40f86a1752b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeff3d5d8b4e6c3a5c831f4d5df564beb30b618851e72ae2b2ce40f86a1752b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/verification/lean_basic_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/lean_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/lean_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/lean_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/lean_basic_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits indented lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/lean_basic_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders structure and theorem helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/lean_basic_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for a missing theorem proof when sorry is disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
