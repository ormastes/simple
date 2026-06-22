# Cli Ops Handlers Specification

> <details>

<!-- sdn-diagram:id=cli_ops_handlers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_ops_handlers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_ops_handlers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_ops_handlers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Ops Handlers Specification

## Scenarios

### Cli Ops Ext

#### returns empty context generation output for unsupported local requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = context_generate("path", "target", "format")
expect(result).to_equal("")
```

</details>

#### returns empty context stats output for unsupported local requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = context_stats("path", "target")
expect(result).to_equal("")
```

</details>

#### returns success for settlement main placeholder implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = settlement_main()
expect(result).to_equal(0)
```

</details>

#### keeps fault configuration hooks callable without changing context stats

1. fault set stack overflow detection
2. fault set stack overflow detection
3. fault set max recursion depth
4. fault set timeout
5. fault set execution limit
   - Expected: context_stats("path", "target") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fault_set_stack_overflow_detection(true)
fault_set_stack_overflow_detection(false)
fault_set_max_recursion_depth(100)
fault_set_timeout(30)
fault_set_execution_limit(1000)

expect(context_stats("path", "target")).to_equal("")
```

</details>

#### returns argument lists from both public argument accessors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = get_args()
val cli_args = cli_get_args()

expect(args.len()).to_be_greater_than(-1)
expect(cli_args.len()).to_be_greater_than(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/cli_ops_handlers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Cli Ops Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
