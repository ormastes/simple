# Repl Basic Eval System Specification

> <details>

<!-- sdn-diagram:id=repl_basic_eval_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=repl_basic_eval_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

repl_basic_eval_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=repl_basic_eval_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repl Basic Eval System Specification

## Scenarios

### REPL Basic Evaluation

<details>
<summary>Advanced: should show banner on startup</summary>

#### should show banner on startup _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl(":quit\n")
expect(output).to_contain("Simple Language REPL")
```

</details>


</details>

<details>
<summary>Advanced: should evaluate print statements</summary>

#### should evaluate print statements _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("print \"hello world\"\n:quit\n")
expect(output).to_contain("hello world")
```

</details>


</details>

<details>
<summary>Advanced: should exit on quit command</summary>

#### should exit on quit command _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl(":quit\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should exit on exit command</summary>

#### should exit on exit command _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("exit\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should show help</summary>

#### should show help _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl(":help\n:quit\n")
expect(output).to_contain("Commands")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/repl/repl_basic_eval_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REPL Basic Evaluation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
