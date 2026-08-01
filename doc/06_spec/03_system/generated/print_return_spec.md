# print_return_spec

> System test for print statement return behavior.

<!-- sdn-diagram:id=print_return_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=print_return_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

print_return_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=print_return_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# print_return_spec

System test for print statement return behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/print_return_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System test for print statement return behavior.

Tests the current print expression return contract.

## Scenarios

### Print Return

#### when printing values

#### returns nil after printing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = print("test")
expect(result).to_be_nil()
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
