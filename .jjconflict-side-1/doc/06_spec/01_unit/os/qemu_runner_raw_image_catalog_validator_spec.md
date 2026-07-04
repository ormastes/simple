# Qemu Runner Raw Image Catalog Validator Specification

> <details>

<!-- sdn-diagram:id=qemu_runner_raw_image_catalog_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_runner_raw_image_catalog_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_runner_raw_image_catalog_validator_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_runner_raw_image_catalog_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Raw Image Catalog Validator Specification

## Scenarios

#### rejects the raw-image fallback when the CLI catalog marker is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-qemu-tool-app-validator-missing"
val bin_dir = root + "/bin"
val img_path = root + "/desktop-uefi-tools.raw"
expect(rt_dir_create_all(bin_dir)).to_equal(true)
expect(shell_exit_code("ln -sf /usr/bin/grep \"" + bin_dir + "/grep\"")).to_equal(0)
expect(shell_exit_code("ln -sf /usr/bin/strings \"" + bin_dir + "/strings\"")).to_equal(0)
expect(rt_file_write_text(img_path, desktop_tool_app_fallback_fixture().replace("info|src/app/info/main.spl|smoke|staged\n", ""))).to_equal(true)

val cmd = "PATH=\"" + bin_dir + "\"; export PATH; " + desktop_uefi_disk_image_tool_app_validation_command(img_path)
expect(shell_status_output(cmd)).to_contain("__exit=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu_runner_raw_image_catalog_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
