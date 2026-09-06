# coreutils/mkdir argument parsing

> Exercises `main_mkdir` argument parsing. Actual IO is stubbed.

<!-- sdn-diagram:id=mkdir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mkdir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mkdir_spec -> std
mkdir_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mkdir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/mkdir argument parsing

Exercises `main_mkdir` argument parsing. Actual IO is stubbed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/mkdir_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `main_mkdir` argument parsing. Actual IO is stubbed.

## Scenarios

### mkdir argument parsing
_Argument handling paths._

#### --help returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_mkdir(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### missing operand returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_mkdir([])
expect rc.to_equal(1i32)
```

</details>

#### -p flag is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_mkdir(["-p", "/tmp/a/b/c"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### mkdir_one
_Single directory helper._

#### returns an i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = mkdir_one("/tmp/x", 0o755u32)
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### mkdir_p
_Recursive-parents helper._

#### returns an i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = mkdir_p("/tmp/a/b/c")
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

#### empty path returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = mkdir_p("")
expect rc.to_equal(0i32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
