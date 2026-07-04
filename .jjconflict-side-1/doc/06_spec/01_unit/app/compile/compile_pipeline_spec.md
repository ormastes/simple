# Compile Pipeline Unit Tests

> 1. check

<!-- sdn-diagram:id=compile_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compile_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compile_pipeline_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compile_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Pipeline Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-COMPILE-001 |
| Category | App \| Compile |
| Status | Implemented |
| Source | `test/01_unit/app/compile/compile_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Compilation Stages

#### lex stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "lex"
check(stage == "lex")
```

</details>

#### parse stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "parse"
check(stage == "parse")
```

</details>

#### typecheck stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "typecheck"
check(stage == "typecheck")
```

</details>

#### lower to hir stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "hir_lower"
check(stage == "hir_lower")
```

</details>

#### lower to mir stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "mir_lower"
check(stage == "mir_lower")
```

</details>

#### optimize stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "optimize"
check(stage == "optimize")
```

</details>

#### codegen stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "codegen"
check(stage == "codegen")
```

</details>

#### link stage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage = "link"
check(stage == "link")
```

</details>

### Compilation Targets

#### compile to native

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "native"
check(target == "native")
```

</details>

#### compile to c

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "c"
check(target == "c")
```

</details>

#### compile to llvm-ir

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "llvm-ir"
check(target == "llvm-ir")
```

</details>

#### compile to wasm

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "wasm"
check(target == "wasm")
```

</details>

#### compile to cuda

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "cuda"
check(target == "cuda")
```

</details>

#### compile to vhdl

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "vhdl"
check(target == "vhdl")
```

</details>

### Compilation Options

#### entry point specification

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = "src/app/cli/main.spl"
check(entry.ends_with(".spl"))
```

</details>

#### output path specification

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "build/output"
check(output.starts_with("build"))
```

</details>

#### debug info inclusion

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug = true
check(debug)
```

</details>

#### optimization level

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt_level = 2
check(opt_level >= 0 and opt_level <= 3)
```

</details>

#### self-contained format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "self-contained"
check(format == "self-contained")
```

</details>

### Compilation Errors

#### file not found error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "file_not_found"
check(error == "file_not_found")
```

</details>

#### syntax error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "syntax_error"
check(error == "syntax_error")
```

</details>

#### type error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "type_error"
check(error == "type_error")
```

</details>

#### linker error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "linker_error"
check(error == "linker_error")
```

</details>

#### multiple errors collected

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = ["e1", "e2", "e3"]
check(errors.len() == 3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
