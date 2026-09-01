# Layer Module Tag Specification

> Tests covering @layer(NAME) module tagging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Module Tag Specification

## Scenarios

### @layer(NAME) module tagging

#### tags a module with a previously-declared layer, no errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tags a module with a previously-declared layer, no errors
   - Expected: parser_has_errors() is false
   - Expected: module.tagged_layer equals `gui`
   - Expected: module.functions contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tags a module with a previously-declared layer, no errors")
val source = "layer gui\n\n@layer(gui)\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_ok.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.tagged_layer).to_equal("gui")
expect(module.functions.contains("main")).to_equal(true)
```

</details>

#### tags a module with a layer declared later in the same file, no errors

- tags a module with a layer declared later in the same file, no errors
   - Expected: parser_has_errors() is false
   - Expected: module.tagged_layer equals `gui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tags a module with a layer declared later in the same file, no errors")
# Validation runs once after the whole decl loop, so source order
# between the `@layer(...)` tag and the `layer NAME` decl it refers
# to must not matter.
val source = "@layer(gui)\n\nlayer gui\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_order.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.tagged_layer).to_equal("gui")
```

</details>

#### is inert: no stray constant/decl is emitted for the marker

- is inert: no stray constant/decl is emitted for the marker
   - Expected: parser_has_errors() is false
   - Expected: module.constants does not contain `_expr_layer_tag_0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is inert: no stray constant/decl is emitted for the marker")
val source = "layer gui\n\n@layer(gui)\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_inert.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.constants.contains("_expr_layer_tag_0")).to_equal(false)
```

</details>

#### leaves untagged modules with an empty tagged_layer

- leaves untagged modules with an empty tagged_layer
   - Expected: parser_has_errors() is false
   - Expected: module.tagged_layer equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves untagged modules with an empty tagged_layer")
val source = "fn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_absent.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.tagged_layer).to_equal("")
```

</details>

#### sabotage: rejects @layer(NAME) when NAME was never declared

- sabotage: rejects @layer(NAME) when NAME was never declared
   - Expected: parser_has_errors() is true
   - Expected: found_layer_dag_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage: rejects @layer(NAME) when NAME was never declared")
val source = "@layer(nonexistent)\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_unknown.spl")

expect(parser_has_errors()).to_equal(true)
val errors = parser_get_errors()
var found_layer_dag_error = false
for e in errors:
    if e.contains("layer_dag"):
        found_layer_dag_error = true
expect(found_layer_dag_error).to_equal(true)
```

</details>

#### sabotage: rejects a bare '@layer()' with no name argument

- sabotage: rejects a bare '@layer()' with no name argument
   - Expected: parser_has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage: rejects a bare '@layer()' with no name argument")
val source = "layer gui\n\n@layer()\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_empty_args.spl")

expect(parser_has_errors()).to_equal(true)
```

</details>

#### does not regress: ordinary decorators (@derive) still parse alongside a layer tag

- does not regress: ordinary decorators (@derive) still parse alongside a layer tag
   - Expected: parser_has_errors() is false
   - Expected: module.tagged_layer equals `gui`
   - Expected: module.structs contains `Point`
   - Expected: module.functions contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not regress: ordinary decorators (@derive) still parse alongside a layer tag")
val source = "layer gui\n\n@layer(gui)\n\n@derive(Eq)\nstruct Point:\n    x: i64\n    y: i64\n\nfn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "layer_tag_broader_regression.spl")

expect(parser_has_errors()).to_equal(false)
expect(module.tagged_layer).to_equal("gui")
expect(module.structs.contains("Point")).to_equal(true)
expect(module.functions.contains("main")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/layer_module_tag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering @layer(NAME) module tagging.
- @layer(NAME) module tagging

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `5e3911476625b83dbcdad2c859b4cceaef6ae9f898bde48429078806413af8c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e3911476625b83dbcdad2c859b4cceaef6ae9f898bde48429078806413af8c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e3911476625b83dbcdad2c859b4cceaef6ae9f898bde48429078806413af8c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/layer_module_tag_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/layer_module_tag_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/layer_module_tag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/layer_module_tag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/layer_module_tag_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tags a module with a previously-declared layer, no errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/layer_module_tag_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tags a module with a layer declared later in the same file, no errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/layer_module_tag_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is inert: no stray constant/decl is emitted for the marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
