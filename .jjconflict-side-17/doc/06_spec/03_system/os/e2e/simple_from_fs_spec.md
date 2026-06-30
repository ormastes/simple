# simple_from_fs_spec

> Two-step end-to-end gate:

<!-- sdn-diagram:id=simple_from_fs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_from_fs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_from_fs_spec -> std
simple_from_fs_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_from_fs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_from_fs_spec

Two-step end-to-end gate:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/e2e/simple_from_fs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Two-step end-to-end gate:
      step 1 — `simple --version` emits a version banner on COM1.
      step 2 — `simple /tmp/hello.spl` prints "ok" to COM1.

    Both steps are gated on SIMPLEOS_SIMPLE_FS_E2E=1 and a built disk image.
    All it-blocks skip cleanly (return a skip-reason string) when the gate
    env var is absent — this is intentional until Tracks F and B''' land.

## Scenarios

### E2E: Simple compiler runs from FAT32 on SimpleOS

#### step 1 [simple-fs-version]: simple --version prints a version banner on COM1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = _gate()
if gate == "":
    return "skip: SIMPLEOS_SIMPLE_FS_E2E not set"
val serial = ensure_serial()
serial.to_contain("Simple ")
```

</details>

#### step 2 [simple-fs-hello]: simple /tmp/hello.spl prints ok on COM1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = _gate()
if gate == "":
    return "skip: SIMPLEOS_SIMPLE_FS_E2E not set"
val serial = ensure_serial()
serial.to_contain("ok")
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
