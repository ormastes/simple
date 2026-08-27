# Compiler Interpret Pipeline Specification

> Tests covering Compiler Interpret Pipeline - Basic Execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Interpret Pipeline Specification

## Scenarios

### Compiler Interpret Pipeline - Basic Execution

#### basic arithmetic fn main succeeds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- basic arithmetic fn main succeeds
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("basic arithmetic fn main succeeds")
val src_path = "/tmp/sml_cip_arith.spl"
write_spl(src_path, "fn main(): 6 * 7")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### variable binding in fn main succeeds

- variable binding in fn main succeeds
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("variable binding in fn main succeeds")
val src_path = "/tmp/sml_cip_vars.spl"
val src = "fn main():" + NL +
    "    val x = 10" + NL +
    "    val y = 20" + NL +
    "    x + y"
write_spl(src_path, src)
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### nested arithmetic in fn main succeeds

- nested arithmetic in fn main succeeds
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested arithmetic in fn main succeeds")
val src_path = "/tmp/sml_cip_nested_arith.spl"
write_spl(src_path, "fn main(): (2 + 3) * 4")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### if else expression in fn main succeeds

- if else expression in fn main succeeds
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if else expression in fn main succeeds")
val src_path = "/tmp/sml_cip_ifelse.spl"
write_spl(src_path, "fn main(): if true: 1 else: 0")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### function call across two fns succeeds

- function call across two fns succeeds
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function call across two fns succeeds")
val src_path = "/tmp/sml_cip_call.spl"
val src = "fn add(a, b): a + b" + NL + "fn main(): add(3, 4)"
write_spl(src_path, src)
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### source without fn main returns success

- source without fn main returns success
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("source without fn main returns success")
val src_path = "/tmp/sml_cip_noname.spl"
write_spl(src_path, "val x = 42")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### struct construction and field access in fn main succeed

- struct construction and field access in fn main succeed
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("struct construction and field access in fn main succeed")
val src_path = "/tmp/sml_cip_struct_field.spl"
val src = "struct Pnt:" + NL +
    "    x: i64" + NL +
    "    y: i64" + NL +
    "fn main():" + NL +
    "    val p = Pnt(x: 7, y: 9)" + NL +
    "    p.x + p.y"
write_spl(src_path, src)
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_interpret_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Compiler Interpret Pipeline - Basic Execution.
- Compiler Interpret Pipeline - Basic Execution

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5bdaeb4323ab555ea573d54af5b678302103dce12e60618c32a19e9363f34cbf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5bdaeb4323ab555ea573d54af5b678302103dce12e60618c32a19e9363f34cbf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5bdaeb4323ab555ea573d54af5b678302103dce12e60618c32a19e9363f34cbf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/compiler_interpret_pipeline_spec.spl
mirror: doc/06_spec/03_system/compiler/compiler_interpret_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/compiler_interpret_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/compiler_interpret_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/compiler_interpret_pipeline_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic arithmetic fn main succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_interpret_pipeline_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'variable binding in fn main succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_interpret_pipeline_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nested arithmetic in fn main succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
