# Bootstrap Self-Compilation

> Tests the bootstrap self-compilation pipeline with lightweight doubles. Verifies that the staged bootstrap process (Rust seed to Simple compiler to self-hosted binary) correctly progresses through each compilation stage.

<!-- sdn-diagram:id=bootstrap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Self-Compilation

Tests the bootstrap self-compilation pipeline with lightweight doubles. Verifies that the staged bootstrap process (Rust seed to Simple compiler to self-hosted binary) correctly progresses through each compilation stage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/bootstrap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the bootstrap self-compilation pipeline with lightweight doubles. Verifies
that the staged bootstrap process (Rust seed to Simple compiler to self-hosted
binary) correctly progresses through each compilation stage.

## Scenarios

### Bootstrap Self-Compilation

#### lexes compiler source into a stable token summary

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main(): 42"
val tokens = fake_lex(source)
check(tokens == "tokens:13")
```

</details>

#### parses source into a stable AST summary

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main(): 42"
val ast = fake_parse(source)
check(ast == "ast:tokens:13")
```

</details>

#### lowers parsed source into a stable HIR summary

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main(): 42"
val hir = fake_lower(fake_parse(source))
check(hir == "hir:ast:tokens:13")
```

</details>

#### generates a stable binary summary

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main(): 42"
val bin = fake_codegen(fake_lower(fake_parse(source)))
check(bin == "bin:hir:ast:tokens:13")
```

</details>

#### bootstrap output is stable across repeated runs

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn bootstrap(): 1"
check(generation_pair(source))
```

</details>

#### bootstrap rejects empty source

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ""
val boot = fake_bootstrap(source)
check(boot == "mir-error")
```

</details>

#### bootstrap summarizes two generations identically

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn self_compile(): 7"
val first = fake_bootstrap(source)
val second = fake_bootstrap(source)
check(first == second)
```

</details>

#### supports a larger source fixture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn outer():\n    val x = 1\n    val y = 2\n    x + y"
val boot = fake_bootstrap(source)
check(boot.starts_with("bin:"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
