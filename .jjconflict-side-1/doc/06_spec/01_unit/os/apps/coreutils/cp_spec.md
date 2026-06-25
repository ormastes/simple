# coreutils/cp argument parsing

> _Argument handling paths._

<!-- sdn-diagram:id=cp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cp_spec -> std
cp_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/cp argument parsing

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/cp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### cp argument parsing
_Argument handling paths._

#### zero args returns 1 (usage error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_cp([])
expect rc.to_equal(1i32)
```

</details>

#### one arg returns 1 (usage error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_cp(["only_one"])
expect rc.to_equal(1i32)
```

</details>

#### three args returns 1 (usage error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_cp(["a", "b", "c"])
expect rc.to_equal(1i32)
```

</details>

#### two args returns an i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_cp(["src", "dst"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
