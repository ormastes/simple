# Compiler Interpret Pipeline Specification

> 1. write spl

<!-- sdn-diagram:id=compiler_interpret_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_interpret_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_interpret_pipeline_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_interpret_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Interpret Pipeline Specification

## Scenarios

### Compiler Interpret Pipeline - Basic Execution

#### basic arithmetic fn main succeeds

1. write spl
   - Expected: result.is_success() is true
2. delete spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_cip_arith.spl"
write_spl(src_path, "fn main(): 6 * 7")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### variable binding in fn main succeeds

1. write spl
   - Expected: result.is_success() is true
2. delete spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write spl
   - Expected: result.is_success() is true
2. delete spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_cip_nested_arith.spl"
write_spl(src_path, "fn main(): (2 + 3) * 4")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### if else expression in fn main succeeds

1. write spl
   - Expected: result.is_success() is true
2. delete spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_cip_ifelse.spl"
write_spl(src_path, "fn main(): if true: 1 else: 0")
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### function call across two fns succeeds

1. write spl
   - Expected: result.is_success() is true
2. delete spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_cip_call.spl"
val src = "fn add(a, b): a + b" + NL + "fn main(): add(3, 4)"
write_spl(src_path, src)
val result = interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_spl(src_path)
```

</details>

#### source without fn main returns success

1. write spl
   - Expected: result.is_success() is true
2. delete spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_cip_noname.spl"
write_spl(src_path, "val x = 42")
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Compiler Interpret Pipeline - Basic Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
