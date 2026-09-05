# Nvme Physical Preflight Script Specification

> <details>

<!-- sdn-diagram:id=nvme_physical_preflight_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_physical_preflight_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_physical_preflight_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_physical_preflight_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Physical Preflight Script Specification

## Scenarios

### SimpleOS physical NVMe preflight wrapper

#### writes scan and selected preflight reports for one ready namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_ready"
val dev = _setup_fake_nvme(base, "nvme8n1", "SNREADY", "1")
val user_dev = _add_fake_nvme_namespace(base, "nvme8n2", "SNREADY", "2")
val report = "/tmp/simpleos_nvme_preflight_script_ready_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_script_ready_selected.sdn"
val cleanup = "rm -f \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"*"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)

val (stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + report + "\" --preflight-out \"" + preflight + "\""
)
val report_text = rt_file_read_text(report) ?? ""
val preflight_text = rt_file_read_text(preflight) ?? ""

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("preflight-scan=ready")
expect(report_text).to_contain("accepted: true")
expect(report_text).to_contain("selected_device: " + dev)
expect(report_text).to_contain("selected_preflight_report: " + preflight)
expect(report_text).to_contain("preflight_identity:")
expect(report_text).to_contain("user_namespace_device: " + user_dev)
expect(preflight_text).to_contain("physical_nvme_preflight:")
expect(preflight_text).to_contain("accepted: true")
expect(preflight_text).to_contain("device: " + dev)
expect(preflight_text).to_contain("user_namespace_device: " + user_dev)
expect(preflight_text).to_contain("same_physical_device: true")
```

</details>

#### requires scan report output before writing selected preflight output

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_requires_report"
val dev = _setup_fake_nvme(base, "nvme8n1", "SNREPORT", "1")
val preflight = "/tmp/simpleos_nvme_preflight_script_requires_report.sdn"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -f \"" + preflight + "\" \"" + preflight + ".tmp.\"*")
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan --preflight-out \"" + preflight + "\""
)
val output_text = rt_file_read_text(preflight) ?? ""

expect(code).to_equal(2)
expect(stderr).to_contain("--preflight-scan --preflight-out requires --report-out")
expect(output_text).to_equal("")
```

</details>

#### rejects scan report and selected preflight output path aliasing

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_same_output"
val dev = _setup_fake_nvme(base, "nvme8n1", "SNSAME", "1")
val output = "/tmp/simpleos_nvme_preflight_script_same_output.sdn"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -f \"" + output + "\" \"" + output + ".tmp.\"*")
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + output + "\" --preflight-out \"" + output + "\""
)
val output_text = rt_file_read_text(output) ?? ""

expect(code).to_equal(2)
expect(stderr).to_contain("--preflight-scan report outputs must differ")
expect(output_text).to_equal("")
```

</details>

#### removes stale selected preflight output before writing a ready scan selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_existing_selected"
val dev = _setup_fake_nvme(base, "nvme8n1", "SNEXISTING", "1")
val user_dev = _add_fake_nvme_namespace(base, "nvme8n2", "SNEXISTING", "2")
val report = "/tmp/simpleos_nvme_preflight_script_existing_selected_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_script_existing_selected.sdn"
val cleanup = "rm -f \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"*"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)
val (_seed_out, _seed_err, seed_code) = _shell("printf 'existing preflight\\n' > \"" + preflight + "\"")
expect(seed_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + report + "\" --preflight-out \"" + preflight + "\""
)
val report_text = rt_file_read_text(report) ?? ""
val preflight_text = rt_file_read_text(preflight) ?? ""

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(report_text).to_contain("accepted: true")
expect(report_text).to_contain("selected_preflight_report: " + preflight)
expect(preflight_text).to_contain("physical_nvme_preflight:")
expect(preflight_text).to_contain("accepted: true")
expect(preflight_text).to_contain("user_namespace_device: " + user_dev)
```

</details>

#### rejects preflight scan when scan report output already exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_existing_scan"
val dev = _setup_fake_nvme(base, "nvme8n1", "SNEXISTINGSCAN", "1")
val report = "/tmp/simpleos_nvme_preflight_script_existing_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_script_existing_scan_selected.sdn"
val cleanup = "rm -f \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"*"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)
val (_seed_out, _seed_err, seed_code) = _shell("printf 'existing scan report\\n' > \"" + report + "\"")
expect(seed_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + report + "\" --preflight-out \"" + preflight + "\""
)
val report_text = rt_file_read_text(report) ?? ""
val preflight_text = rt_file_read_text(preflight) ?? ""

expect(code).to_equal(2)
expect(stderr).to_contain("preflight scan report already exists")
expect(report_text).to_equal("existing scan report\n")
expect(preflight_text).to_equal("")
```

</details>

#### removes selected preflight temp output when scan is not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_not_ready"
val dev = _setup_fake_nvme(base, "nvme8n1", "SNNOTREADY", "1")
val report = "/tmp/simpleos_nvme_preflight_script_not_ready_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_script_not_ready_selected.sdn"
val cleanup = "rm -f \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"*"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + report + "\" --preflight-out \"" + preflight + "\""
)
val report_text = rt_file_read_text(report) ?? ""
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e \"" + preflight + "\" && ! ls " + preflight + ".tmp.* >/dev/null 2>&1")

expect(code).to_equal(1)
expect(stderr).to_contain("preflight-scan=not-ready")
expect(report_text).to_contain("status: not-ready")
expect(probe_code).to_equal(0)
```

</details>

#### writes a not-ready scan report when no namespace devices match

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_no_match"
val dev_dir = base + "_device"
val report = "/tmp/simpleos_nvme_preflight_script_no_match_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_script_no_match_selected.sdn"
val cleanup = "rm -rf \"" + dev_dir + "\" && rm -f \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"*"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)
val (_mkdir_out, _mkdir_err, mkdir_code) = _shell("mkdir -p \"" + dev_dir + "\"")
expect(mkdir_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev_dir + "/nvme*n1\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + report + "\" --preflight-out \"" + preflight + "\""
)
val report_text = rt_file_read_text(report) ?? ""
val (_probe_out, _probe_err, probe_code) = _shell(
    "test ! -e \"" + preflight + "\" && " +
    "! ls " + preflight + ".tmp.* >/dev/null 2>&1 && " +
    "! grep -q selected_preflight_report \"" + report + "\""
)

expect(code).to_equal(1)
expect(stderr).to_contain("preflight-scan=not-ready matched_devices=0 ready_devices=0")
expect(report_text).to_contain("accepted: false")
expect(report_text).to_contain("status: not-ready")
expect(report_text).to_contain("matched_devices: 0")
expect(report_text).to_contain("ready_devices: 0")
expect(probe_code).to_equal(0)
```

</details>

#### does not write selected preflight output when scan is ambiguous

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simpleos_nvme_preflight_script_ambiguous"
val dev_a = _setup_fake_nvme(base, "nvme8n1", "SNAMBIGA", "1")
val _user_dev_a = _add_fake_nvme_namespace(base, "nvme8n2", "SNAMBIGA", "2")
val dev_b = _add_fake_nvme_namespace(base, "nvme9n1", "SNAMBIGB", "1")
val _user_dev_b = _add_fake_nvme_namespace(base, "nvme9n2", "SNAMBIGB", "2")
val report = "/tmp/simpleos_nvme_preflight_script_ambiguous_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_script_ambiguous_selected.sdn"
val cleanup = "rm -f \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"*"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "SIMPLEOS_NVME_DEVICE_GLOB=\"" + dev_a + " " + dev_b + "\" " +
    "SIMPLEOS_NVME_SYSFS_ROOT=\"" + base + "_sysfs\" " +
    "sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan " +
    "--report-out \"" + report + "\" --preflight-out \"" + preflight + "\""
)
val report_text = rt_file_read_text(report) ?? ""
val (_probe_out, _probe_err, probe_code) = _shell(
    "test ! -e \"" + preflight + "\" && " +
    "! ls " + preflight + ".tmp.* >/dev/null 2>&1 && " +
    "! grep -q selected_preflight_report \"" + report + "\""
)

expect(code).to_equal(1)
expect(stderr).to_contain("preflight-scan=ambiguous")
expect(report_text).to_contain("status: ambiguous")
expect(report_text).to_contain("ready_devices: 2")
expect(report_text).to_contain("candidates: " + dev_a + " " + dev_b)
expect(probe_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_physical_preflight_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS physical NVMe preflight wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
