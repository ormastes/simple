# Repl Commands System Specification

> <details>

<!-- sdn-diagram:id=repl_commands_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=repl_commands_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

repl_commands_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=repl_commands_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repl Commands System Specification

## Scenarios

### REPL Commands

<details>
<summary>Advanced: should handle :quit</summary>

#### should handle :quit _(slow)_

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
<summary>Advanced: should handle :q shorthand</summary>

#### should handle :q shorthand _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl(":q\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should handle :clear</summary>

#### should handle :clear _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl(":clear\n:quit\n")
expect(output).to_contain("State cleared")
```

</details>


</details>

<details>
<summary>Advanced: should handle :history</summary>

#### should handle :history _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("val x = 1\n:history\n:quit\n")
expect(output).to_contain("val x = 1")
```

</details>


</details>

<details>
<summary>Advanced: should handle :show</summary>

#### should handle :show _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("val x = 1\n:show\n:quit\n")
expect(output).to_contain("val x = 1")
```

</details>


</details>

<details>
<summary>Advanced: should handle exit() function call</summary>

#### should handle exit() function call _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_repl("exit()\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should terminate on EOF</summary>

#### should terminate on EOF _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("bash", ["-c", "echo '' | " + find_simple_binary() + " run src/app/repl/main.spl 2>/dev/null"])
expect(code).to_equal(0)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/repl/repl_commands_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REPL Commands

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
