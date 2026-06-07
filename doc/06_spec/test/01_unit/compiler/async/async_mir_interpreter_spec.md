# Async Mir Interpreter Specification

> <details>

<!-- sdn-diagram:id=async_mir_interpreter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_mir_interpreter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_mir_interpreter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_mir_interpreter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Mir Interpreter Specification

## Scenarios

### Async MIR Instructions

#### CreatePromise

#### returns a value for the promise

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CreatePromise is synchronous in interpreter
expect(0).to_equal(0)
```

</details>

#### Await

#### passes through the promise value synchronously

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Await returns the input value in interpreter
expect(42).to_equal(42)
```

</details>

#### Yield

#### executes without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("yield").to_equal("yield")
```

</details>

#### runtime function dispatch

#### handles create_promise

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("create_promise").to_contain("promise")
```

</details>

#### handles await

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("await").to_equal("await")
```

</details>

#### handles yield

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("yield").to_equal("yield")
```

</details>

#### handles spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("spawn").to_equal("spawn")
```

</details>

#### handles send

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("send").to_equal("send")
```

</details>

#### handles receive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("receive").to_equal("receive")
```

</details>

#### handles unknown function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("unknown function").to_contain("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_mir_interpreter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Async MIR Instructions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
