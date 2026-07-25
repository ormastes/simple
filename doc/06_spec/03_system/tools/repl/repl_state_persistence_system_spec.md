# Repl State Persistence System Specification

> <details>

<!-- sdn-diagram:id=repl_state_persistence_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=repl_state_persistence_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

repl_state_persistence_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=repl_state_persistence_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repl State Persistence System Specification

## Scenarios

### REPL State Persistence

<details>
<summary>Advanced: should persist val definitions</summary>

#### should persist val definitions _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("val x = 42\nprint x\n:quit\n")
expect(output).to_contain("42")
```

</details>


</details>

<details>
<summary>Advanced: should persist var definitions</summary>

#### should persist var definitions _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("var y = 10\nprint y\n:quit\n")
expect(output).to_contain("10")
```

</details>


</details>

<details>
<summary>Advanced: should persist function definitions</summary>

#### should persist function definitions _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input_text = "fn double(n: i64) -> i64:\n    n * 2\n\nprint double(21)\n:quit\n"
val output = run_repl(input_text)
expect(output).to_contain("42")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/repl/repl_state_persistence_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REPL State Persistence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
