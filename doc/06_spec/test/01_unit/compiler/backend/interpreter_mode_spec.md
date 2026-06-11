# Interpreter Mode Specification

> <details>

<!-- sdn-diagram:id=interpreter_mode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_mode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_mode_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_mode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Mode Specification

## Scenarios

### Interpreter Mode

#### creates the default hybrid JIT config

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInterpreterConfig(
    mode: JitMode.Auto,
    backend: "auto",
    jit_threshold: 10,
    verbose: false
)

expect(config.mode).to_equal(JitMode.Auto)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_equal(10)
expect(config.verbose).to_equal(false)
```

</details>

#### creates an always-interpret config

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInterpreterConfig(
    mode: JitMode.AlwaysInterpret,
    backend: "auto",
    jit_threshold: 999999,
    verbose: false
)

expect(config.mode).to_equal(JitMode.AlwaysInterpret)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_be_greater_than(1000)
expect(config.verbose).to_equal(false)
```

</details>

#### creates an always-jit config

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInterpreterConfig(
    mode: JitMode.AlwaysJit,
    backend: "auto",
    jit_threshold: 0,
    verbose: false
)

expect(config.mode).to_equal(JitMode.AlwaysJit)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_equal(0)
expect(config.verbose).to_equal(false)
```

</details>

#### creates a thresholded auto-jit config

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInterpreterConfig(
    mode: JitMode.Auto,
    backend: "auto",
    jit_threshold: 1,
    verbose: false
)

expect(config.mode).to_equal(JitMode.Auto)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_equal(1)
expect(config.verbose).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/interpreter_mode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Interpreter Mode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
