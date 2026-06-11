# Interpreter Backend Specification

> <details>

<!-- sdn-diagram:id=interpreter_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_backend_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Backend Specification

## Scenarios

### Interpreter Backend

#### creates a backend port with stable metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = create_interpreter_backend()
val target_triple = backend.target_triple_fn
val supports_jit = backend.supports_jit_fn

expect(backend.name).to_equal("interpreter")
expect(target_triple()).to_equal("interpreter-simple-runtime")
expect(supports_jit()).to_equal(true)
```

</details>

#### returns an independent backend port per factory call

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = create_interpreter_backend()
val second = create_interpreter_backend()
val first_target_triple = first.target_triple_fn
val second_target_triple = second.target_triple_fn
val first_supports_jit = first.supports_jit_fn
val second_supports_jit = second.supports_jit_fn

expect(first.name).to_equal(second.name)
expect(first_target_triple()).to_equal(second_target_triple())
expect(first_supports_jit()).to_equal(second_supports_jit())
```

</details>

#### provides a callable run function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = create_interpreter_backend()

expect(backend.run_fn).to_equal(backend.run_fn)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/interpreter_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Interpreter Backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
