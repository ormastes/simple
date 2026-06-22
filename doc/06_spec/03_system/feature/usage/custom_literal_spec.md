# Custom Literal Syntax

> Tests the custom collection literal syntax, specifically the `s{...}` prefix for set literals. Verifies that set literals are distinguished from ordinary identifiers and blocks, handles nested set literals with correct depth tracking, and rejects malformed custom literal expressions.

<!-- sdn-diagram:id=custom_literal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_literal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_literal_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_literal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Literal Syntax

Tests the custom collection literal syntax, specifically the `s{...}` prefix for set literals. Verifies that set literals are distinguished from ordinary identifiers and blocks, handles nested set literals with correct depth tracking, and rejects malformed custom literal expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/custom_literal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the custom collection literal syntax, specifically the `s{...}` prefix for set
literals. Verifies that set literals are distinguished from ordinary identifiers and
blocks, handles nested set literals with correct depth tracking, and rejects malformed
custom literal expressions.

## Scenarios

### Custom Literals

#### distinguishes set literals from variables

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(is_custom_set_literal("s{1, 2, 3}"))
check(not is_custom_set_literal("s"))
check(not is_custom_set_literal("value {1, 2, 3}"))
```

</details>

#### handles nested set literals

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(is_custom_set_literal("s{1, s{2, 3}}"))
check(nested_literal_depth("s{1, s{2, 3}}") == 2)
check(nested_literal_depth("s{1, 2, 3}") == 1)
```

</details>

#### rejects malformed custom literals

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not is_custom_set_literal("s{1, 2, 3"))
check(not is_custom_set_literal("{1, 2, 3}"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
