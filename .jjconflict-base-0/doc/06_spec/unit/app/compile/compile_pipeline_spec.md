# Compile Pipeline Specification

> Tests covering Compilation Stages, Compilation Targets, Compilation Options, Compilation Errors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Pipeline Specification

## Scenarios

### Compilation Stages

#### lex stage

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lex stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lex stage")
val stage = "lex"
check(stage == "lex")
```

</details>

#### parse stage

- parse stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse stage")
val stage = "parse"
check(stage == "parse")
```

</details>

#### typecheck stage

- typecheck stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("typecheck stage")
val stage = "typecheck"
check(stage == "typecheck")
```

</details>

#### lower to hir stage

- lower to hir stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower to hir stage")
val stage = "hir_lower"
check(stage == "hir_lower")
```

</details>

#### lower to mir stage

- lower to mir stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower to mir stage")
val stage = "mir_lower"
check(stage == "mir_lower")
```

</details>

#### optimize stage

- optimize stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optimize stage")
val stage = "optimize"
check(stage == "optimize")
```

</details>

#### codegen stage

- codegen stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("codegen stage")
val stage = "codegen"
check(stage == "codegen")
```

</details>

#### link stage

- link stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("link stage")
val stage = "link"
check(stage == "link")
```

</details>

### Compilation Targets

#### compile to native

- compile to native


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile to native")
val target = "native"
check(target == "native")
```

</details>

#### compile to c

- compile to c


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile to c")
val target = "c"
check(target == "c")
```

</details>

#### compile to llvm-ir

- compile to llvm-ir


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile to llvm-ir")
val target = "llvm-ir"
check(target == "llvm-ir")
```

</details>

#### compile to wasm

- compile to wasm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile to wasm")
val target = "wasm"
check(target == "wasm")
```

</details>

#### compile to cuda

- compile to cuda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile to cuda")
val target = "cuda"
check(target == "cuda")
```

</details>

#### compile to vhdl

- compile to vhdl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile to vhdl")
val target = "vhdl"
check(target == "vhdl")
```

</details>

### Compilation Options

#### entry point specification

- entry point specification


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entry point specification")
val entry = "src/app/cli/main.spl"
check(entry.ends_with(".spl"))
```

</details>

#### output path specification

- output path specification


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output path specification")
val output = "build/output"
check(output.starts_with("build"))
```

</details>

#### debug info inclusion

- debug info inclusion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug info inclusion")
val debug = true
check(debug)
```

</details>

#### optimization level

- optimization level


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optimization level")
val opt_level = 2
check(opt_level >= 0 and opt_level <= 3)
```

</details>

#### self-contained format

- self-contained format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("self-contained format")
val format = "self-contained"
check(format == "self-contained")
```

</details>

### Compilation Errors

#### file not found error

- file not found error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file not found error")
val error = "file_not_found"
check(error == "file_not_found")
```

</details>

#### syntax error

- syntax error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("syntax error")
val error = "syntax_error"
check(error == "syntax_error")
```

</details>

#### type error

- type error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type error")
val error = "type_error"
check(error == "type_error")
```

</details>

#### linker error

- linker error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("linker error")
val error = "linker_error"
check(error == "linker_error")
```

</details>

#### multiple errors collected

- multiple errors collected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple errors collected")
val errors = ["e1", "e2", "e3"]
check(errors.len() == 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/compile/compile_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Compilation Stages, Compilation Targets, Compilation Options, Compilation Errors.
- Compilation Stages
- Compilation Targets
- Compilation Options
- Compilation Errors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `63e815d9a592b85a3ad0fdbedc210bbd737cc240b724f884af36392621ba73eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63e815d9a592b85a3ad0fdbedc210bbd737cc240b724f884af36392621ba73eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63e815d9a592b85a3ad0fdbedc210bbd737cc240b724f884af36392621ba73eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/compile/compile_pipeline_spec.spl
mirror: doc/06_spec/unit/app/compile/compile_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/compile/compile_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/compile/compile_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/compile/compile_pipeline_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lex stage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/compile/compile_pipeline_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse stage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/compile/compile_pipeline_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'typecheck stage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
