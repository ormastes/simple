# Remove Self Parameters Specification

> Unit tests for the remove_self_params migration tool. This refactoring eliminates explicit `self` parameter declarations from method definitions, making methods implicitly reference `self` instead.

<!-- sdn-diagram:id=remove_self_params_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remove_self_params_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remove_self_params_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remove_self_params_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remove Self Parameters Specification

Unit tests for the remove_self_params migration tool. This refactoring eliminates explicit `self` parameter declarations from method definitions, making methods implicitly reference `self` instead.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Tooling-Refactor-RemoveSelfParams |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/remove_self_params_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the remove_self_params migration tool. This refactoring eliminates
explicit `self` parameter declarations from method definitions, making methods
implicitly reference `self` instead.

## Behavior

The migration handles:
- Removal of explicit `self` parameters from method signatures
- Preservation of method functionality and semantics
- Proper handling of immutable and mutable methods
- Static method preservation (no self parameter)

## Implementation Notes

This is a compiler-assisted refactoring pass that simplifies method declarations
by leveraging implicit `self` availability in all methods.

## Scenarios

### remove_self_params module compiles

#### basic sanity check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
