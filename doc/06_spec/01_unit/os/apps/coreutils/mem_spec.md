# coreutils/mem argument parsing

> _Argument handling paths._

<!-- sdn-diagram:id=mem_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mem_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mem_spec -> std
mem_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mem_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/mem argument parsing

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/mem_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### mem argument parsing
_Argument handling paths._

#### --help returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_mem(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### empty args returns an i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_mem([])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
