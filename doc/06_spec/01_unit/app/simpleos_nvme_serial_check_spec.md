# Simpleos Nvme Serial Check Specification

> <details>

<!-- sdn-diagram:id=simpleos_nvme_serial_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_nvme_serial_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_nvme_serial_check_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_nvme_serial_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Nvme Serial Check Specification

## Scenarios

### SimpleOS physical NVMe serial checker app

#### exits zero for real NVMe evidence and nonzero for q35 emulator evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_serial_check_ready.log"
val q35_path = "/tmp/simpleos_nvme_serial_check_q35.log"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(q35_path)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val q35_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("q35", "true", "emulator") + "TEST PASSED\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
expect(rt_file_write_text(q35_path, q35_log)).to_equal(true)

val (ready_stdout, _ready_stderr, ready_code) = _run_checker(ready_path)
val (q35_stdout, _q35_stderr, q35_code) = _run_checker(q35_path)

expect(ready_code).to_equal(0)
expect(ready_stdout).to_contain("reason=ready")
expect(q35_code).to_equal(1)
expect(q35_stdout).to_contain("reason=missing-physical-nvme-marker:hardware_target=real-nvme")
```

</details>

#### writes an auditable validation report for accepted and rejected logs

<details>
<summary>Executable SSpec</summary>

Runnable source: 77 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_report_ready.log"
val q35_path = "/tmp/simpleos_nvme_report_q35.log"
val ready_report = "/tmp/simpleos_nvme_report_ready.sdn"
val q35_report = "/tmp/simpleos_nvme_report_q35.sdn"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(q35_path)
val _ = rt_file_delete(ready_report)
val _ = rt_file_delete(q35_report)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val q35_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("q35", "true", "emulator") + "TEST PASSED\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
expect(rt_file_write_text(q35_path, q35_log)).to_equal(true)

val (_ready_stdout, _ready_stderr, ready_code) = _run_checker_with_report(ready_path, ready_report)
val (_q35_stdout, _q35_stderr, q35_code) = _run_checker_with_report(q35_path, q35_report)
val ready_report_text = rt_file_read_text(ready_report) ?? ""
val q35_report_text = rt_file_read_text(q35_report) ?? ""

expect(ready_code).to_equal(0)
expect(ready_report_text).to_contain("accepted: true")
expect(ready_report_text).to_contain("reason: ready")
expect(ready_report_text).to_contain("hardware_target: real-nvme")
expect(ready_report_text).to_contain("qemu: false")
expect(ready_report_text).to_contain("device_model: Samsung_PM9A3")
expect(ready_report_text).to_contain("device_serial: SN123456")
expect(ready_report_text).to_contain("namespace_nsid: 1")
expect(ready_report_text).to_contain("measured_on: real-device")
expect(ready_report_text).to_contain("user_namespace:")
expect(ready_report_text).to_contain("assignment: hardware-data-queue")
expect(ready_report_text).to_contain("nsid: 2")
expect(ready_report_text).to_contain("queue_id: 2")
expect(ready_report_text).to_contain("active_lease_count: 1")
expect(ready_report_text).to_contain("shared_interface: fat32,nvfs,dbfs")
expect(ready_report_text).to_contain("conflict_policy: active-lease-checked")
expect(ready_report_text).to_contain("filesystems:")
expect(ready_report_text).to_contain("consumers: fat32,nvfs,dbfs")
expect(ready_report_text).to_contain("fat32_direct_io: read-write-through")
expect(ready_report_text).to_contain("nvfs_direct_io: read-write-through")
expect(ready_report_text).to_contain("dbfs_direct_io: read-write-through")
expect(ready_report_text).to_contain("fat32_extent_source: freestanding-fat32-extents")
expect(ready_report_text).to_contain("nvfs_extent_source: freestanding-dbfs-arena")
expect(ready_report_text).to_contain("dbfs_extent_source: freestanding-dbfs-arena")
expect(ready_report_text).to_contain("c_baseline:")
expect(ready_report_text).to_contain("bridge_used: false")
expect(ready_report_text).to_contain("device: same-nvme")
expect(ready_report_text).to_contain("scope: in-guest")
expect(ready_report_text).to_contain("cache: direct")
expect(ready_report_text).to_contain("vfat_baseline:")
expect(ready_report_text).to_contain("filesystem: vfat")
expect(ready_report_text).to_contain("performance:")
expect(ready_report_text).to_contain("simple_read_iops: 120000")
expect(ready_report_text).to_contain("simple_write_iops: 90000")
expect(ready_report_text).to_contain("simple_read_p99_us: 800")
expect(ready_report_text).to_contain("simple_write_p99_us: 1000")
expect(ready_report_text).to_contain("c_read_iops: 100000")
expect(ready_report_text).to_contain("c_write_iops: 80000")
expect(ready_report_text).to_contain("c_read_p99_us: 900")
expect(ready_report_text).to_contain("c_write_p99_us: 1100")
expect(ready_report_text).to_contain("queue_depth: 64")
expect(ready_report_text).to_contain("warm_runs: 5")
expect(ready_report_text).to_contain("max_rss_kib: 32768")
expect(ready_report_text).to_contain("optimization_contract:")
expect(ready_report_text).to_contain("acceptance_reason: ready")
expect(ready_report_text).to_contain("validated_faster_than_c: true")
expect(ready_report_text).to_contain("c_bridge_used: false")
expect(ready_report_text).to_contain("common_logic_shared: true")
expect(ready_report_text).to_contain("allocation_per_io: false")
expect(ready_report_text).to_contain("workload: 4k-random-read-write")
expect(ready_report_text).to_contain("io_size_bytes: 4096")
expect(q35_code).to_equal(1)
expect(q35_report_text).to_contain("accepted: false")
expect(q35_report_text).to_contain("acceptance_reason: missing-physical-nvme-marker:hardware_target=real-nvme")
expect(q35_report_text).to_contain("validated_faster_than_c: false")
expect(q35_report_text).to_contain("hardware_target: q35")
expect(q35_report_text).to_contain("measured_on: emulator")
expect(q35_report_text).to_contain("missing-physical-nvme-marker:hardware_target=real-nvme")
```

</details>

#### fails when the validation report cannot be written

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_report_write_failure.log"
val missing_report = "/tmp/simpleos_nvme_missing_report_dir/report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf /tmp/simpleos_nvme_missing_report_dir \"" + ready_path + "\""], 5000)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)

val (stdout, _stderr, code) = _run_checker_with_report(ready_path, missing_report)

expect(code).to_equal(1)
expect(stdout).to_contain("validation-report-write-failed")
```

</details>

#### keeps the physical NVMe lab wrapper fail-closed in validate-log-only mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_lab_wrapper_ready.log"
val q35_path = "/tmp/simpleos_nvme_lab_wrapper_q35.log"
val empty_path = "/tmp/simpleos_nvme_lab_wrapper_empty.log"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(q35_path)
val _ = rt_file_delete(empty_path)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val q35_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("q35", "true", "emulator") + "TEST PASSED\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
expect(rt_file_write_text(q35_path, q35_log)).to_equal(true)
expect(rt_file_write_text(empty_path, "")).to_equal(true)

val (ready_stdout, _ready_stderr, ready_code) = _run_lab_wrapper(ready_path)
val (q35_stdout, _q35_stderr, q35_code) = _run_lab_wrapper(q35_path)
val (_empty_stdout, empty_stderr, empty_code) = _run_lab_wrapper(empty_path)

expect(ready_code).to_equal(0)
expect(ready_stdout).to_contain("reason=ready")
expect(q35_code).to_equal(1)
expect(q35_stdout).to_contain("reason=missing-physical-nvme-marker:hardware_target=real-nvme")
expect(empty_code).to_equal(1)
expect(empty_stderr).to_contain("serial log is empty")
```

</details>

#### rejects duplicate NVMe perf reports through the checker and lab wrapper

1.  physical nvme perf marker
2.  physical nvme perf marker
   - Expected: rt_file_write_text(duplicate_path, ready_log) is true
   - Expected: checker_code equals `1`
   - Expected: wrapper_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duplicate_path = "/tmp/simpleos_nvme_duplicate_perf.log"
val duplicate_report = "/tmp/simpleos_nvme_duplicate_perf.sdn"
val _ = rt_file_delete(duplicate_path)
val _report = rt_file_delete(duplicate_report)
val ready_log = _physical_nvme_access_marker() +
    _physical_nvme_perf_marker("real-nvme", "false", "real-device") +
    _physical_nvme_perf_marker("real-nvme", "false", "real-device") +
    "TEST PASSED\n"
expect(rt_file_write_text(duplicate_path, ready_log)).to_equal(true)

val (checker_stdout, _checker_stderr, checker_code) = _run_checker(duplicate_path)
val (wrapper_stdout, _wrapper_stderr, wrapper_code) = _run_lab_wrapper_with_report(duplicate_path, duplicate_report)
val report_text = rt_file_read_text(duplicate_report) ?? ""

expect(checker_code).to_equal(1)
expect(checker_stdout).to_contain("multiple-nvme-perf-reports")
expect(wrapper_code).to_equal(1)
expect(wrapper_stdout).to_contain("multiple-nvme-perf-reports")
expect(report_text).to_contain("accepted: false")
expect(report_text).to_contain("acceptance_reason: nvme-real-hardware-perf:multiple-nvme-perf-reports")
```

</details>

#### rejects duplicate critical NVMe perf fields in a single report

1. ready perf replace
2. ready perf replace
   - Expected: rt_file_write_text(qemu_path, qemu_spoof_log) is true
   - Expected: rt_file_write_text(vfat_path, vfat_spoof_log) is true
   - Expected: rt_file_write_text(user_nsid_path, user_nsid_spoof_log) is true
   - Expected: qemu_code equals `1`
   - Expected: vfat_code equals `1`
   - Expected: user_nsid_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qemu_path = "/tmp/simpleos_nvme_duplicate_qemu_field.log"
val vfat_path = "/tmp/simpleos_nvme_duplicate_vfat_field.log"
val user_nsid_path = "/tmp/simpleos_nvme_duplicate_user_nsid_field.log"
val qemu_report = "/tmp/simpleos_nvme_duplicate_qemu_field.sdn"
val vfat_report = "/tmp/simpleos_nvme_duplicate_vfat_field.sdn"
val user_nsid_report = "/tmp/simpleos_nvme_duplicate_user_nsid_field.sdn"
val _ = rt_file_delete(qemu_path)
val _ = rt_file_delete(vfat_path)
val _user_nsid_cleanup = rt_file_delete(user_nsid_path)
val _ = rt_file_delete(qemu_report)
val _ = rt_file_delete(vfat_report)
val _user_nsid_report_cleanup = rt_file_delete(user_nsid_report)
val ready_perf = _physical_nvme_perf_marker("real-nvme", "false", "real-device")
val qemu_spoof_log = _physical_nvme_access_marker() +
    ready_perf.replace("\n", " qemu=true\n") +
    "TEST PASSED\n"
val vfat_spoof_log = _physical_nvme_access_marker() +
    ready_perf.replace("\n", " vfat_baseline_device=host-cache\n") +
    "TEST PASSED\n"
val user_nsid_spoof_log = _physical_nvme_access_marker().replace("\n", " user_namespace_nsid=1\n") +
    ready_perf +
    "TEST PASSED\n"
expect(rt_file_write_text(qemu_path, qemu_spoof_log)).to_equal(true)
expect(rt_file_write_text(vfat_path, vfat_spoof_log)).to_equal(true)
expect(rt_file_write_text(user_nsid_path, user_nsid_spoof_log)).to_equal(true)

val (qemu_stdout, _qemu_stderr, qemu_code) = _run_checker_with_report(qemu_path, qemu_report)
val (vfat_stdout, _vfat_stderr, vfat_code) = _run_checker_with_report(vfat_path, vfat_report)
val (user_nsid_stdout, _user_nsid_stderr, user_nsid_code) = _run_checker_with_report(user_nsid_path, user_nsid_report)
val qemu_report_text = rt_file_read_text(qemu_report) ?? ""
val vfat_report_text = rt_file_read_text(vfat_report) ?? ""
val user_nsid_report_text = rt_file_read_text(user_nsid_report) ?? ""

expect(qemu_code).to_equal(1)
expect(qemu_stdout).to_contain("duplicate-nvme-perf-field:qemu=")
expect(qemu_report_text).to_contain("accepted: false")
expect(qemu_report_text).to_contain("acceptance_reason: nvme-real-hardware-perf:duplicate-nvme-perf-field:qemu=")
expect(vfat_code).to_equal(1)
expect(vfat_stdout).to_contain("duplicate-nvme-perf-field:vfat_baseline_device=")
expect(vfat_report_text).to_contain("accepted: false")
expect(vfat_report_text).to_contain("acceptance_reason: nvme-real-hardware-perf:duplicate-nvme-perf-field:vfat_baseline_device=")
expect(user_nsid_code).to_equal(1)
expect(user_nsid_stdout).to_contain("duplicate-nvme-perf-field:user_namespace_nsid=")
expect(user_nsid_report_text).to_contain("accepted: false")
expect(user_nsid_report_text).to_contain("acceptance_reason: nvme-real-hardware-perf:duplicate-nvme-perf-field:user_namespace_nsid=")
```

</details>

#### rejects production perf evidence without same-device VFAT baseline markers

1. ready perf replace
2. ready perf replace
   - Expected: rt_file_write_text(missing_path, missing_log) is true
   - Expected: rt_file_write_text(spoof_path, spoofed_log) is true
   - Expected: missing_code equals `1`
   - Expected: spoof_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = "/tmp/simpleos_nvme_missing_vfat_baseline.log"
val spoof_path = "/tmp/simpleos_nvme_spoofed_vfat_baseline.log"
val missing_report = "/tmp/simpleos_nvme_missing_vfat_baseline.sdn"
val spoof_report = "/tmp/simpleos_nvme_spoofed_vfat_baseline.sdn"
val _ = rt_file_delete(missing_path)
val _ = rt_file_delete(spoof_path)
val _ = rt_file_delete(missing_report)
val _ = rt_file_delete(spoof_report)
val ready_perf = _physical_nvme_perf_marker("real-nvme", "false", "real-device")
val missing_log = _physical_nvme_access_marker() +
    ready_perf.replace("vfat_baseline_device=same-nvme ", "") +
    "TEST PASSED\n"
val spoofed_log = _physical_nvme_access_marker() +
    ready_perf.replace("vfat_baseline_device=same-nvme", "vfat_baseline_device=host-cache") +
    "TEST PASSED\n"
expect(rt_file_write_text(missing_path, missing_log)).to_equal(true)
expect(rt_file_write_text(spoof_path, spoofed_log)).to_equal(true)

val (missing_stdout, _missing_stderr, missing_code) = _run_checker_with_report(missing_path, missing_report)
val (spoof_stdout, _spoof_stderr, spoof_code) = _run_checker_with_report(spoof_path, spoof_report)
val missing_report_text = rt_file_read_text(missing_report) ?? ""
val spoof_report_text = rt_file_read_text(spoof_report) ?? ""

expect(missing_code).to_equal(1)
expect(missing_stdout).to_contain("missing-physical-nvme-marker:vfat_baseline_device=same-nvme")
expect(missing_report_text).to_contain("accepted: false")
expect(missing_report_text).to_contain("device: unknown")
expect(spoof_code).to_equal(1)
expect(spoof_stdout).to_contain("missing-physical-nvme-marker:vfat_baseline_device=same-nvme")
expect(spoof_report_text).to_contain("accepted: false")
expect(spoof_report_text).to_contain("device: host-cache")
```

</details>

#### rejects invalid live serial capture settings before capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial_path = "/tmp/simpleos_nvme_invalid_capture_settings.log"
val _ = rt_file_delete(serial_path)

val (_bad_baud_stdout, bad_baud_stderr, bad_baud_code) = _run_lab_wrapper_live_capture_settings(serial_path, "fast", "30")
val (_zero_seconds_stdout, zero_seconds_stderr, zero_seconds_code) = _run_lab_wrapper_live_capture_settings(serial_path, "115200", "0")
val (_bad_seconds_stdout, bad_seconds_stderr, bad_seconds_code) = _run_lab_wrapper_live_capture_settings(serial_path, "115200", "many")
val (_missing_port_stdout, missing_port_stderr, missing_port_code) = _run_lab_wrapper_live_capture_settings(serial_path, "115200", "30")

expect(bad_baud_code).to_equal(2)
expect(bad_baud_stderr).to_contain("SERIAL_BAUD must be a positive integer")
expect(zero_seconds_code).to_equal(2)
expect(zero_seconds_stderr).to_contain("SIMPLEOS_NVME_SERIAL_SECONDS must be a positive integer")
expect(bad_seconds_code).to_equal(2)
expect(bad_seconds_stderr).to_contain("SIMPLEOS_NVME_SERIAL_SECONDS must be a positive integer")
expect(missing_port_code).to_equal(2)
expect(missing_port_stderr).to_contain("serial port not found")
```

</details>

#### passes report output through the physical NVMe lab wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_lab_wrapper_report_ready.log"
val ready_report = "/tmp/simpleos_nvme_lab_wrapper_report_ready.sdn"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(ready_report)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)

val (_ready_stdout, _ready_stderr, ready_code) = _run_lab_wrapper_with_report(ready_path, ready_report)
val ready_report_text = rt_file_read_text(ready_report) ?? ""

expect(ready_code).to_equal(0)
expect(ready_report_text).to_contain("accepted: true")
expect(ready_report_text).to_contain("device_serial: SN123456")
expect(ready_report_text).to_contain("nsid: 2")
expect(ready_report_text).to_contain("active_lease_count: 1")
expect(ready_report_text).to_contain("consumers: fat32,nvfs,dbfs")
expect(ready_report_text).to_contain("fat32_direct_io: read-write-through")
expect(ready_report_text).to_contain("device: same-nvme")
expect(ready_report_text).to_contain("simple_read_iops: 120000")
expect(ready_report_text).to_contain("c_read_iops: 100000")
expect(ready_report_text).to_contain("gate: real_device_physical_nvme_serial_acceptance_reason")

val (_overwrite_stdout, overwrite_stderr, overwrite_code) = _run_lab_wrapper_with_report(ready_path, ready_report)
expect(overwrite_code).to_equal(2)
expect(overwrite_stderr).to_contain("validation report already exists")
```

</details>

#### requires serial identity to match the host preflight report when supplied

<details>
<summary>Executable SSpec</summary>

Runnable source: 355 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_identity_compare_ready.log"
val preflight_report = "/tmp/simpleos_nvme_identity_compare_preflight.sdn"
val missing_file_preflight = "/tmp/simpleos_nvme_identity_compare_missing_file.sdn"
val missing_file_report = "/tmp/simpleos_nvme_identity_compare_missing_file_report.sdn"
val invalid_report = "/tmp/simpleos_nvme_identity_compare_invalid.sdn"
val not_accepted_report = "/tmp/simpleos_nvme_identity_compare_not_accepted.sdn"
val missing_schema_report = "/tmp/simpleos_nvme_identity_compare_missing_schema.sdn"
val bad_checker_report = "/tmp/simpleos_nvme_identity_compare_bad_checker.sdn"
val model_report = "/tmp/simpleos_nvme_identity_compare_model.sdn"
val mismatch_report = "/tmp/simpleos_nvme_identity_compare_mismatch.sdn"
val user_namespace_report = "/tmp/simpleos_nvme_identity_compare_user_namespace.sdn"
val missing_user_device_report = "/tmp/simpleos_nvme_identity_compare_user_device.sdn"
val same_user_device_report = "/tmp/simpleos_nvme_identity_compare_same_user_device.sdn"
val user_model_report = "/tmp/simpleos_nvme_identity_compare_user_model.sdn"
val user_serial_report = "/tmp/simpleos_nvme_identity_compare_user_serial.sdn"
val prefix_report = "/tmp/simpleos_nvme_identity_compare_prefix.sdn"
val duplicate_preflight_report = "/tmp/simpleos_nvme_identity_compare_duplicate_preflight.sdn"
val match_report = "/tmp/simpleos_nvme_identity_compare_match.sdn"
val multi_report = "/tmp/simpleos_nvme_identity_compare_multi.sdn"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(preflight_report)
val _ = rt_file_delete(missing_file_preflight)
val _ = rt_file_delete(missing_file_report)
val _ = rt_file_delete(invalid_report)
val _ = rt_file_delete(not_accepted_report)
val _ = rt_file_delete(missing_schema_report)
val _ = rt_file_delete(bad_checker_report)
val _ = rt_file_delete(model_report)
val _ = rt_file_delete(mismatch_report)
val _ = rt_file_delete(user_namespace_report)
val _ = rt_file_delete(missing_user_device_report)
val _ = rt_file_delete(same_user_device_report)
val _ = rt_file_delete(user_model_report)
val _ = rt_file_delete(user_serial_report)
val _ = rt_file_delete(prefix_report)
val _duplicate_preflight_report_cleanup = rt_file_delete(duplicate_preflight_report)
val _ = rt_file_delete(match_report)
val _ = rt_file_delete(multi_report)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val invalid_preflight = "serial: SN123456\nnamespace_nsid: 1\n"
val not_accepted_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: false\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val same_user_device_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n1\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val missing_schema_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val bad_checker_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: /tmp/not-the-simpleos-checker.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val model_mismatch_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: DIFFERENT\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n"
val mismatch_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: DIFFERENT\n" +
    "    namespace_nsid: 1\n"
val prefix_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN1234567\n" +
    "    namespace_nsid: 1\n"
val user_namespace_mismatch_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_nsid: 3\n"
val missing_user_device_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val user_model_mismatch_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: DIFFERENT\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val user_serial_mismatch_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: DIFFERENT\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val duplicate_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    serial: DIFFERENT\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val matching_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
val multi_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme*n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "  device: /dev/nvme10n1\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
val (_missing_file_stdout, _missing_file_stderr, missing_file_code) = _run_checker_with_preflight(ready_path, missing_file_preflight, missing_file_report)
val missing_file_text = rt_file_read_text(missing_file_report) ?? ""
expect(missing_file_code).to_equal(1)
expect(missing_file_text).to_contain("reason: physical-nvme-preflight-report-invalid")
expect(missing_file_text).to_contain("preflight_report_loaded: false")
expect(missing_file_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, invalid_preflight)).to_equal(true)
val (_invalid_stdout, _invalid_stderr, invalid_code) = _run_checker_with_preflight(ready_path, preflight_report, invalid_report)
val invalid_text = rt_file_read_text(invalid_report) ?? ""
expect(invalid_code).to_equal(1)
expect(invalid_text).to_contain("reason: physical-nvme-preflight-report-invalid")
expect(invalid_text).to_contain("preflight_report_loaded: true")
expect(invalid_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, not_accepted_preflight)).to_equal(true)
val (_not_accepted_stdout, _not_accepted_stderr, not_accepted_code) = _run_checker_with_preflight(ready_path, preflight_report, not_accepted_report)
val not_accepted_text = rt_file_read_text(not_accepted_report) ?? ""
expect(not_accepted_code).to_equal(1)
expect(not_accepted_text).to_contain("reason: physical-nvme-preflight-not-accepted")
expect(not_accepted_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, missing_schema_preflight)).to_equal(true)
val (_schema_stdout, _schema_stderr, schema_code) = _run_checker_with_preflight(ready_path, preflight_report, missing_schema_report)
val schema_text = rt_file_read_text(missing_schema_report) ?? ""
expect(schema_code).to_equal(1)
expect(schema_text).to_contain("reason: physical-nvme-preflight-glob-missing")
expect(schema_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, bad_checker_preflight)).to_equal(true)
val (_checker_stdout, _checker_stderr, checker_code) = _run_checker_with_preflight(ready_path, preflight_report, bad_checker_report)
val checker_text = rt_file_read_text(bad_checker_report) ?? ""
expect(checker_code).to_equal(1)
expect(checker_text).to_contain("reason: physical-nvme-preflight-checker-invalid")
expect(checker_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, model_mismatch_preflight)).to_equal(true)
val (_model_stdout, _model_stderr, model_code) = _run_checker_with_preflight(ready_path, preflight_report, model_report)
val model_text = rt_file_read_text(model_report) ?? ""
expect(model_code).to_equal(1)
expect(model_text).to_contain("reason: physical-nvme-preflight-model-mismatch")
expect(model_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, mismatch_preflight)).to_equal(true)
val (_mismatch_stdout, _mismatch_stderr, mismatch_code) = _run_checker_with_preflight(ready_path, preflight_report, mismatch_report)
val mismatch_text = rt_file_read_text(mismatch_report) ?? ""
expect(mismatch_code).to_equal(1)
expect(mismatch_text).to_contain("reason: physical-nvme-preflight-serial-mismatch")
expect(mismatch_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, prefix_preflight)).to_equal(true)
val (_prefix_stdout, _prefix_stderr, prefix_code) = _run_checker_with_preflight(ready_path, preflight_report, prefix_report)
val prefix_text = rt_file_read_text(prefix_report) ?? ""
expect(prefix_code).to_equal(1)
expect(prefix_text).to_contain("reason: physical-nvme-preflight-serial-mismatch")
expect(prefix_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, user_namespace_mismatch_preflight)).to_equal(true)
val (_user_ns_stdout, _user_ns_stderr, user_ns_code) = _run_checker_with_preflight(ready_path, preflight_report, user_namespace_report)
val user_ns_text = rt_file_read_text(user_namespace_report) ?? ""
expect(user_ns_code).to_equal(1)
expect(user_ns_text).to_contain("reason: physical-nvme-preflight-user-namespace-mismatch")
expect(user_ns_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, missing_user_device_preflight)).to_equal(true)
val (_user_device_stdout, _user_device_stderr, user_device_code) = _run_checker_with_preflight(ready_path, preflight_report, missing_user_device_report)
val user_device_text = rt_file_read_text(missing_user_device_report) ?? ""
expect(user_device_code).to_equal(1)
expect(user_device_text).to_contain("reason: physical-nvme-preflight-user-namespace-device-missing")
expect(user_device_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, same_user_device_preflight)).to_equal(true)
val (_same_user_device_stdout, _same_user_device_stderr, same_user_device_code) = _run_checker_with_preflight(ready_path, preflight_report, same_user_device_report)
val same_user_device_text = rt_file_read_text(same_user_device_report) ?? ""
expect(same_user_device_code).to_equal(1)
expect(same_user_device_text).to_contain("reason: physical-nvme-preflight-user-namespace-device-conflicts-system")
expect(same_user_device_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, user_model_mismatch_preflight)).to_equal(true)
val (_user_model_stdout, _user_model_stderr, user_model_code) = _run_checker_with_preflight(ready_path, preflight_report, user_model_report)
val user_model_text = rt_file_read_text(user_model_report) ?? ""
expect(user_model_code).to_equal(1)
expect(user_model_text).to_contain("reason: physical-nvme-preflight-user-namespace-model-mismatch")
expect(user_model_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, user_serial_mismatch_preflight)).to_equal(true)
val (_user_serial_stdout, _user_serial_stderr, user_serial_code) = _run_checker_with_preflight(ready_path, preflight_report, user_serial_report)
val user_serial_text = rt_file_read_text(user_serial_report) ?? ""
expect(user_serial_code).to_equal(1)
expect(user_serial_text).to_contain("reason: physical-nvme-preflight-user-namespace-serial-mismatch")
expect(user_serial_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, duplicate_preflight)).to_equal(true)
val (_duplicate_preflight_stdout, _duplicate_preflight_stderr, duplicate_preflight_code) = _run_checker_with_preflight(ready_path, preflight_report, duplicate_preflight_report)
val duplicate_preflight_text = rt_file_read_text(duplicate_preflight_report) ?? ""
expect(duplicate_preflight_code).to_equal(1)
expect(duplicate_preflight_text).to_contain("reason: physical-nvme-preflight-duplicate-field:serial")
expect(duplicate_preflight_text).to_contain("preflight_identity_match: false")

expect(rt_file_write_text(preflight_report, matching_preflight)).to_equal(true)
val (_match_stdout, _match_stderr, match_code) = _run_checker_with_preflight(ready_path, preflight_report, match_report)
val match_text = rt_file_read_text(match_report) ?? ""
expect(match_code).to_equal(0)
expect(match_text).to_contain("reason: ready")
expect(match_text).to_contain("preflight_identity_match: true")

expect(rt_file_write_text(preflight_report, multi_preflight)).to_equal(true)
val (_multi_stdout, _multi_stderr, multi_code) = _run_checker_with_preflight(ready_path, preflight_report, multi_report)
val multi_text = rt_file_read_text(multi_report) ?? ""
expect(multi_code).to_equal(1)
expect(multi_text).to_contain("reason: physical-nvme-preflight-multiple-devices")
expect(multi_text).to_contain("preflight_identity_match: false")
```

</details>

#### loads supplied preflight evidence even when serial evidence is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q35_path = "/tmp/simpleos_nvme_rejected_with_preflight.log"
val preflight_report = "/tmp/simpleos_nvme_rejected_with_preflight_preflight.sdn"
val report = "/tmp/simpleos_nvme_rejected_with_preflight_report.sdn"
val _ = rt_file_delete(q35_path)
val _ = rt_file_delete(preflight_report)
val _ = rt_file_delete(report)
val q35_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("q35", "true", "emulator") + "TEST PASSED\n"
val matching_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"

expect(rt_file_write_text(q35_path, q35_log)).to_equal(true)
expect(rt_file_write_text(preflight_report, matching_preflight)).to_equal(true)

val (_stdout, _stderr, code) = _run_checker_with_preflight(q35_path, preflight_report, report)
val report_text = rt_file_read_text(report) ?? ""

expect(code).to_equal(1)
expect(report_text).to_contain("reason: missing-physical-nvme-marker:hardware_target=real-nvme")
expect(report_text).to_contain("preflight_report_loaded: true")
expect(report_text).to_contain("model: Samsung PM9A3")
expect(report_text).to_contain("preflight_identity_match: false")
```

</details>

#### passes preflight identity comparison through the physical NVMe lab wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_lab_wrapper_identity_compare.log"
val preflight_report = "/tmp/simpleos_nvme_lab_wrapper_identity_preflight.sdn"
val report = "/tmp/simpleos_nvme_lab_wrapper_identity_compare.sdn"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(preflight_report)
val _ = rt_file_delete(report)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val matching_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
expect(rt_file_write_text(preflight_report, matching_preflight)).to_equal(true)

val (_stdout, _stderr, code) = _run_lab_wrapper_with_preflight(ready_path, preflight_report, report)
val report_text = rt_file_read_text(report) ?? ""

expect(code).to_equal(0)
expect(report_text).to_contain("preflight_report: " + preflight_report)
expect(report_text).to_contain("preflight_report_loaded: true")
expect(report_text).to_contain("preflight_identity:")
expect(report_text).to_contain("device: /dev/nvme9n1")
expect(report_text).to_contain("controller: nvme9")
expect(report_text).to_contain("model: Samsung PM9A3")
expect(report_text).to_contain("serial: SN123456")
expect(report_text).to_contain("namespace_nsid: 1")
expect(report_text).to_contain("user_namespace_device: /dev/nvme9n2")
expect(report_text).to_contain("user_namespace_controller: nvme9")
expect(report_text).to_contain("user_namespace_model: Samsung PM9A3")
expect(report_text).to_contain("user_namespace_serial: SN123456")
expect(report_text).to_contain("user_namespace_nsid: 2")
expect(report_text).to_contain("user_namespace_same_controller: true")
expect(report_text).to_contain("same_physical_device: true")
expect(report_text).to_contain("preflight_identity_match: true")
```

</details>

#### rejects supplied preflight identity without same-device markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_lab_wrapper_missing_same_device.log"
val preflight_report = "/tmp/simpleos_nvme_lab_wrapper_missing_same_device_preflight.sdn"
val report = "/tmp/simpleos_nvme_lab_wrapper_missing_same_device_report.sdn"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(preflight_report)
val _ = rt_file_delete(report)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val missing_marker_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
expect(rt_file_write_text(preflight_report, missing_marker_preflight)).to_equal(true)

val (_stdout, _stderr, code) = _run_lab_wrapper_with_preflight(ready_path, preflight_report, report)
val report_text = rt_file_read_text(report) ?? ""

expect(code).to_equal(1)
expect(report_text).to_contain("reason: physical-nvme-preflight-same-physical-device-marker-missing")
expect(report_text).to_contain("preflight_identity_match: false")
```

</details>

#### requires preflight identity and validation report in production wrapper mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_path = "/tmp/simpleos_nvme_lab_wrapper_production.log"
val preflight_report = "/tmp/simpleos_nvme_lab_wrapper_production_preflight.sdn"
val missing_preflight_report = "/tmp/simpleos_nvme_lab_wrapper_production_missing_preflight.sdn"
val empty_preflight_report = "/tmp/simpleos_nvme_lab_wrapper_production_empty_preflight.sdn"
val report = "/tmp/simpleos_nvme_lab_wrapper_production_report.sdn"
val _ = rt_file_delete(ready_path)
val _ = rt_file_delete(preflight_report)
val _ = rt_file_delete(missing_preflight_report)
val _ = rt_file_delete(empty_preflight_report)
val _ = rt_file_delete(report)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val matching_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_device: /dev/nvme9n2\n" +
    "    user_namespace_controller: nvme9\n" +
    "    user_namespace_model: Samsung PM9A3\n" +
    "    user_namespace_serial: SN123456\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"

expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
val (_missing_stdout, missing_stderr, missing_code) = _run_lab_wrapper_production_without_preflight(ready_path, report)
expect(missing_code).to_equal(2)
expect(missing_stderr).to_contain("--production requires --preflight-report or --preflight-out")

val (_missing_file_stdout, missing_file_stderr, missing_file_code) = _run_lab_wrapper_production(ready_path, missing_preflight_report, report)
expect(missing_file_code).to_equal(1)
expect(missing_file_stderr).to_contain("preflight report not found")

expect(rt_file_write_text(empty_preflight_report, "")).to_equal(true)
val (_empty_stdout, empty_stderr, empty_code) = _run_lab_wrapper_production(ready_path, empty_preflight_report, report)
expect(empty_code).to_equal(1)
expect(empty_stderr).to_contain("preflight report is empty")

expect(rt_file_write_text(preflight_report, matching_preflight)).to_equal(true)
expect(rt_file_write_text(report, "old report\n")).to_equal(true)
val (_existing_stdout, existing_stderr, existing_code) = _run_lab_wrapper_production(ready_path, preflight_report, report)
expect(existing_code).to_equal(2)
expect(existing_stderr).to_contain("validation report already exists")
val _report_cleanup = rt_file_delete(report)

val (_stdout, _stderr, code) = _run_lab_wrapper_production(ready_path, preflight_report, report)
val report_text = rt_file_read_text(report) ?? ""

expect(code).to_equal(0)
expect(report_text).to_contain("preflight_identity:")
expect(report_text).to_contain("user_namespace_device: /dev/nvme9n2")
expect(report_text).to_contain("user_namespace_model: Samsung PM9A3")
expect(report_text).to_contain("user_namespace_serial: SN123456")
expect(report_text).to_contain("preflight_identity_match: true")
```

</details>

#### rejects generated production preflight when validating a pre-existing serial log

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_preflight_out_sysfs"
val fake_dev = "/tmp/simpleos_nvme_production_preflight_out_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val ready_path = "/tmp/simpleos_nvme_production_preflight_out.log"
val preflight_out = "/tmp/simpleos_nvme_production_preflight_out.sdn"
val report = "/tmp/simpleos_nvme_production_preflight_out_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + preflight_out + "\" \"" + report + "\" \"" + ready_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"$(dirname \"" + fake_dev + "\")\""], 5000)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)

val (_stdout, stderr, code) = _run_lab_wrapper_production_with_preflight_out(ready_path, fake_dev, fake_root, preflight_out, report)

expect(code).to_equal(2)
expect(stderr).to_contain("--production --preflight-out requires live serial capture")
```

</details>

#### rejects generated production preflight before comparing a stale serial identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_preflight_mismatch_sysfs"
val fake_dev = "/tmp/simpleos_nvme_production_preflight_mismatch_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val ready_path = "/tmp/simpleos_nvme_production_preflight_mismatch.log"
val preflight_out = "/tmp/simpleos_nvme_production_preflight_mismatch.sdn"
val report = "/tmp/simpleos_nvme_production_preflight_mismatch_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + preflight_out + "\" \"" + report + "\" \"" + ready_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"$(dirname \"" + fake_dev + "\")\""], 5000)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "DIFFERENT\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)

val (_stdout, stderr, code) = _run_lab_wrapper_production_with_preflight_out(ready_path, fake_dev, fake_root, preflight_out, report)

expect(code).to_equal(2)
expect(stderr).to_contain("--production --preflight-out requires live serial capture")
```

</details>

#### rejects ambiguous or aliased production evidence paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_preflight_alias_sysfs"
val fake_dev = "/tmp/simpleos_nvme_production_preflight_alias_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val ready_path = "/tmp/simpleos_nvme_production_preflight_alias.log"
val preflight_report = "/tmp/simpleos_nvme_production_preflight_alias_reported.sdn"
val preflight_out = "/tmp/simpleos_nvme_production_preflight_alias.sdn"
val report = "/tmp/simpleos_nvme_production_preflight_alias_validation.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + preflight_report + "\" \"" + preflight_out + "\" \"" + report + "\" \"" + ready_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"$(dirname \"" + fake_dev + "\")\""], 5000)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
val matching_preflight =
    "physical_nvme_preflight:\n" +
    "  accepted: true\n" +
    "  nvme_device_glob: /dev/nvme9n1\n" +
    "  checker: src/app/simpleos_nvme_serial_check/main.spl\n" +
    "  device: /dev/nvme9n1\n" +
    "    controller: nvme9\n" +
    "    model: Samsung PM9A3\n" +
    "    serial: SN123456\n" +
    "    namespace_nsid: 1\n" +
    "    user_namespace_nsid: 2\n" +
    "    user_namespace_same_controller: true\n" +
    "    same_physical_device: true\n"
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)
expect(rt_file_write_text(preflight_report, matching_preflight)).to_equal(true)

val (_both_stdout, both_stderr, both_code) = _run_lab_wrapper_production_with_both_preflight_paths(ready_path, preflight_report, fake_dev, fake_root, preflight_out, report)
val (_same_report_stdout, same_report_stderr, same_report_code) = _run_lab_wrapper_production_with_preflight_out(ready_path, fake_dev, fake_root, report, report)
val (_same_serial_stdout, same_serial_stderr, same_serial_code) = _run_lab_wrapper_production_with_preflight_out(ready_path, fake_dev, fake_root, ready_path, report)
val (_same_validation_stdout, same_validation_stderr, same_validation_code) = _run_lab_wrapper_production(ready_path, preflight_report, ready_path)

expect(both_code).to_equal(2)
expect(both_stderr).to_contain("not both")
expect(same_report_code).to_equal(2)
expect(same_report_stderr).to_contain("--preflight-out must differ from --report-out")
expect(same_serial_code).to_equal(2)
expect(same_serial_stderr).to_contain("--preflight-out must differ from --serial-log")
expect(same_validation_code).to_equal(2)
expect(same_validation_stderr).to_contain("--report-out must differ from --serial-log")
```

</details>

#### rejects one-shot production when evidence output paths already exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_existing_output_sysfs"
val fake_dev = "/tmp/simpleos_nvme_production_existing_output_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val serial_path = "/tmp/simpleos_nvme_production_existing_output.log"
val preflight_out = "/tmp/simpleos_nvme_production_existing_output_preflight.sdn"
val report = "/tmp/simpleos_nvme_production_existing_output_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + preflight_out + "\" \"" + report + "\" \"" + serial_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"$(dirname \"" + fake_dev + "\")\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)

expect(rt_file_write_text(serial_path, "old serial\n")).to_equal(true)
val (_serial_stdout, serial_stderr, serial_code) = _run_lab_wrapper_live_production_with_preflight_out(serial_path, fake_dev, fake_root, preflight_out, report)
expect(serial_code).to_equal(2)
expect(serial_stderr).to_contain("serial log already exists")
val _serial_cleanup = rt_file_delete(serial_path)

expect(rt_file_write_text(preflight_out, "old preflight\n")).to_equal(true)
val (_preflight_stdout, preflight_stderr, preflight_code) = _run_lab_wrapper_live_production_with_preflight_out(serial_path, fake_dev, fake_root, preflight_out, report)
expect(preflight_code).to_equal(2)
expect(preflight_stderr).to_contain("preflight output already exists")
val _preflight_cleanup = rt_file_delete(preflight_out)

expect(rt_file_write_text(report, "old report\n")).to_equal(true)
val (_report_stdout, report_stderr, report_code) = _run_lab_wrapper_live_production_with_preflight_out(serial_path, fake_dev, fake_root, preflight_out, report)
expect(report_code).to_equal(2)
expect(report_stderr).to_contain("validation report already exists")
```

</details>

#### does not leave selected preflight evidence when live production serial capture cannot start

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_serial_missing_sysfs"
val fake_dev = "/tmp/simpleos_nvme_production_serial_missing_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val fake_user_sysfs = fake_root + "/nvme9n2"
val serial_path = "/tmp/simpleos_nvme_production_serial_missing.log"
val preflight_out = "/tmp/simpleos_nvme_production_serial_missing_preflight.sdn"
val report = "/tmp/simpleos_nvme_production_serial_missing_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + preflight_out + "\" \"" + preflight_out + ".tmp.\"* \"" + report + "\" \"" + serial_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_user_sysfs + "/device\" \"$(dirname \"" + fake_dev + "\")\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/nsid", "2\n")).to_equal(true)

val (_stdout, stderr, code) = _run_lab_wrapper_live_production_with_preflight_out(serial_path, fake_dev, fake_root, preflight_out, report)
val preflight_text = rt_file_read_text(preflight_out) ?? ""
val report_text = rt_file_read_text(report) ?? ""
val serial_text = rt_file_read_text(serial_path) ?? ""
val (_tmp_stdout, _tmp_stderr, tmp_code) = rt_process_run_timeout("/bin/sh", ["-c", "test -z \"$(ls " + preflight_out + ".tmp.* 2>/dev/null)\""], 5000)

expect(code).to_equal(2)
expect(stderr).to_contain("serial port not found")
expect(preflight_text).to_equal("")
expect(report_text).to_equal("")
expect(serial_text).to_equal("")
expect(tmp_code).to_equal(0)
```

</details>

#### rejects one-shot production when host preflight identity is incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_preflight_unknown_sysfs"
val fake_dev = "/tmp/simpleos_nvme_production_preflight_unknown_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val ready_path = "/tmp/simpleos_nvme_production_preflight_unknown.log"
val preflight_out = "/tmp/simpleos_nvme_production_preflight_unknown.sdn"
val report = "/tmp/simpleos_nvme_production_preflight_unknown_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + preflight_out + "\" \"" + report + "\" \"" + ready_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"$(dirname \"" + fake_dev + "\")\""], 5000)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)

val (_stdout, stderr, code) = _run_lab_wrapper_production_with_preflight_out(ready_path, fake_dev, fake_root, preflight_out, report)

expect(code).to_equal(2)
expect(stderr).to_contain("--production --preflight-out requires live serial capture")
```

</details>

#### rejects one-shot production when the host device glob is ambiguous

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_production_preflight_multi_sysfs"
val fake_dev_a = "/tmp/simpleos_nvme_production_preflight_multi_device/nvme9n1"
val fake_dev_b = "/tmp/simpleos_nvme_production_preflight_multi_device/nvme10n1"
val fake_sysfs_a = fake_root + "/nvme9n1"
val fake_sysfs_b = fake_root + "/nvme10n1"
val fake_glob = fake_dev_a + " " + fake_dev_b
val ready_path = "/tmp/simpleos_nvme_production_preflight_multi.log"
val preflight_out = "/tmp/simpleos_nvme_production_preflight_multi.sdn"
val report = "/tmp/simpleos_nvme_production_preflight_multi_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev_a + "\" \"" + fake_dev_b + "\" \"" + preflight_out + "\" \"" + report + "\" \"" + ready_path + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs_a + "/device\" \"" + fake_sysfs_b + "/device\" \"$(dirname \"" + fake_dev_a + "\")\""], 5000)
val ready_log = _physical_nvme_access_marker() + _physical_nvme_perf_marker("real-nvme", "false", "real-device") + "TEST PASSED\n"
expect(rt_file_write_text(fake_dev_a, "device-a")).to_equal(true)
expect(rt_file_write_text(fake_dev_b, "device-b")).to_equal(true)
expect(rt_file_write_text(fake_sysfs_a + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs_a + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs_a + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs_b + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs_b + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs_b + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(ready_path, ready_log)).to_equal(true)

val (_stdout, stderr, code) = _run_lab_wrapper_production_with_preflight_out(ready_path, fake_glob, fake_root, preflight_out, report)

expect(code).to_equal(2)
expect(stderr).to_contain("--production --preflight-out requires live serial capture")
```

</details>

#### preflights the physical NVMe lab environment before serial capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_status_sysfs"
val fake_nvme = "/tmp/simpleos_nvme_preflight_status_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val fake_user_sysfs = fake_root + "/nvme9n2"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_nvme + "\" && mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_user_sysfs + "/device\" \"$(dirname \"" + fake_nvme + "\")\""], 5000)
expect(rt_file_write_text(fake_nvme, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/nsid", "2\n")).to_equal(true)

val (stdout, _stderr, code) = _run_lab_preflight_with_sysfs(fake_nvme, fake_root)

expect(code).to_equal(0)
expect(stdout).to_contain("preflight=ready")
expect(stdout).to_contain("checker=present")
```

</details>

#### rejects standalone preflight when identity cannot be proven

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_nvme = "/tmp/simpleos_nvme_preflight_no_identity_device"
val _ = rt_file_delete(fake_nvme)
expect(rt_file_write_text(fake_nvme, "device")).to_equal(true)

val (_stdout, stderr, code) = _run_lab_preflight(fake_nvme)

expect(code).to_equal(1)
expect(stderr).to_contain("incomplete NVMe sysfs identity")
```

</details>

#### rejects standalone preflight when the device glob is ambiguous

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_dir = "/tmp/simpleos_nvme_preflight_multi_device"
val fake_a = fake_dir + "/nvme9n1"
val fake_b = fake_dir + "/nvme10n1"
val fake_glob = fake_dir + "/nvme*n1"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_dir + "\" && mkdir -p \"" + fake_dir + "\""], 5000)
expect(rt_file_write_text(fake_a, "device-a")).to_equal(true)
expect(rt_file_write_text(fake_b, "device-b")).to_equal(true)

val (_stdout, stderr, code) = _run_lab_preflight(fake_glob)

expect(code).to_equal(1)
expect(stderr).to_contain("production preflight requires exactly one NVMe namespace device; matched 2")
```

</details>

#### scans candidate NVMe namespaces and selects the one with a distinct user namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_scan_sysfs"
val fake_dir = "/tmp/simpleos_nvme_preflight_scan_device"
val fake_bad = fake_dir + "/nvme8n1"
val fake_good = fake_dir + "/nvme9n1"
val fake_glob = fake_dir + "/nvme*n1"
val fake_bad_sysfs = fake_root + "/nvme8n1"
val fake_good_sysfs = fake_root + "/nvme9n1"
val fake_good_user_sysfs = fake_root + "/nvme9n2"
val report = "/tmp/simpleos_nvme_preflight_scan.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_scan_selected.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dir + "\" \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"* && mkdir -p \"" + fake_bad_sysfs + "/device\" \"" + fake_good_sysfs + "/device\" \"" + fake_good_user_sysfs + "/device\" \"" + fake_dir + "\""], 5000)
expect(rt_file_write_text(fake_bad, "bad")).to_equal(true)
expect(rt_file_write_text(fake_good, "good")).to_equal(true)
expect(rt_file_write_text(fake_bad_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_bad_sysfs + "/device/serial", "SNBAD\n")).to_equal(true)
expect(rt_file_write_text(fake_bad_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_good_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_good_sysfs + "/device/serial", "SNGOOD\n")).to_equal(true)
expect(rt_file_write_text(fake_good_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_good_user_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_good_user_sysfs + "/device/serial", "SNGOOD\n")).to_equal(true)
expect(rt_file_write_text(fake_good_user_sysfs + "/nsid", "2\n")).to_equal(true)

val (stdout, stderr, code) = _run_lab_preflight_scan_report_and_preflight_with_sysfs(fake_glob, fake_root, report, preflight)
val report_text = rt_file_read_text(report) ?? ""
val preflight_text = rt_file_read_text(preflight) ?? ""

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("preflight-scan device=" + fake_bad + " status=failed")
expect(stdout).to_contain("preflight-scan device=" + fake_good + " status=ready")
expect(stdout).to_contain("preflight-scan=ready matched_devices=2 ready_devices=1 selected_device=" + fake_good)
expect(report_text).to_contain("physical_nvme_preflight_scan:")
expect(report_text).to_contain("device: " + fake_bad)
expect(report_text).to_contain("status: failed")
expect(report_text).to_contain("device: " + fake_good)
expect(report_text).to_contain("preflight_identity:")
expect(report_text).to_contain("physical_nvme_preflight:")
expect(report_text).to_contain("user_namespace_device: " + "/tmp/simpleos_nvme_preflight_scan_device/nvme9n2")
expect(report_text).to_contain("user_namespace_same_controller: true")
expect(report_text).to_contain("same_physical_device: true")
expect(report_text).to_contain("accepted: true")
expect(report_text).to_contain("status: ready")
expect(report_text).to_contain("selected_device: " + fake_good)
expect(preflight_text).to_contain("physical_nvme_preflight:")
expect(preflight_text).to_contain("accepted: true")
expect(preflight_text).to_contain("device: " + fake_good)
expect(preflight_text).to_contain("user_namespace_device: " + "/tmp/simpleos_nvme_preflight_scan_device/nvme9n2")
expect(preflight_text).to_contain("same_physical_device: true")
```

</details>

#### rejects preflight scan when multiple namespaces are production-ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_scan_ambiguous_sysfs"
val fake_dir = "/tmp/simpleos_nvme_preflight_scan_ambiguous_device"
val fake_a = fake_dir + "/nvme8n1"
val fake_b = fake_dir + "/nvme9n1"
val fake_glob = fake_dir + "/nvme*n1"
val fake_a_sysfs = fake_root + "/nvme8n1"
val fake_a_user_sysfs = fake_root + "/nvme8n2"
val fake_b_sysfs = fake_root + "/nvme9n1"
val fake_b_user_sysfs = fake_root + "/nvme9n2"
val report = "/tmp/simpleos_nvme_preflight_scan_ambiguous.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_scan_ambiguous_selected.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dir + "\" \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"* && mkdir -p \"" + fake_a_sysfs + "/device\" \"" + fake_a_user_sysfs + "/device\" \"" + fake_b_sysfs + "/device\" \"" + fake_b_user_sysfs + "/device\" \"" + fake_dir + "\""], 5000)
expect(rt_file_write_text(fake_a, "a")).to_equal(true)
expect(rt_file_write_text(fake_b, "b")).to_equal(true)
expect(rt_file_write_text(fake_a_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_a_sysfs + "/device/serial", "SNA\n")).to_equal(true)
expect(rt_file_write_text(fake_a_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_a_user_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_a_user_sysfs + "/device/serial", "SNA\n")).to_equal(true)
expect(rt_file_write_text(fake_a_user_sysfs + "/nsid", "2\n")).to_equal(true)
expect(rt_file_write_text(fake_b_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_b_sysfs + "/device/serial", "SNB\n")).to_equal(true)
expect(rt_file_write_text(fake_b_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_b_user_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_b_user_sysfs + "/device/serial", "SNB\n")).to_equal(true)
expect(rt_file_write_text(fake_b_user_sysfs + "/nsid", "2\n")).to_equal(true)

val (stdout, stderr, code) = _run_lab_preflight_scan_report_and_preflight_with_sysfs(fake_glob, fake_root, report, preflight)
val report_text = rt_file_read_text(report) ?? ""
val preflight_text = rt_file_read_text(preflight) ?? ""

expect(code).to_equal(1)
expect(stdout).to_contain("preflight-scan device=" + fake_a + " status=ready")
expect(stdout).to_contain("preflight-scan device=" + fake_b + " status=ready")
expect(stderr).to_contain("preflight-scan=ambiguous matched_devices=2 ready_devices=2")
expect(stderr).to_contain("candidates=" + fake_a + " " + fake_b)
expect(report_text).to_contain("accepted: false")
expect(report_text).to_contain("status: ambiguous")
expect(report_text).to_contain("matched_devices: 2")
expect(report_text).to_contain("ready_devices: 2")
expect(report_text).to_contain("candidates: " + fake_a + " " + fake_b)
expect(preflight_text).to_equal("")
```

</details>

#### writes a not-ready preflight scan report when no namespace has a distinct user namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_scan_not_ready_sysfs"
val fake_dir = "/tmp/simpleos_nvme_preflight_scan_not_ready_device"
val fake_dev = fake_dir + "/nvme8n1"
val fake_sysfs = fake_root + "/nvme8n1"
val report = "/tmp/simpleos_nvme_preflight_scan_not_ready.sdn"
val preflight = "/tmp/simpleos_nvme_preflight_scan_not_ready_selected.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dir + "\" \"" + report + "\" \"" + report + ".tmp.\"* \"" + preflight + "\" \"" + preflight + ".tmp.\"* && mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_dir + "\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SNNOUSER\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)

val (stdout, stderr, code) = _run_lab_preflight_scan_report_and_preflight_with_sysfs(fake_dev, fake_root, report, preflight)
val report_text = rt_file_read_text(report) ?? ""
val (_preflight_probe_stdout, _preflight_probe_stderr, preflight_probe_code) = rt_process_run_timeout("/bin/sh", ["-c", "test ! -e \"" + preflight + "\" && ! ls " + preflight + ".tmp.* >/dev/null 2>&1"], 5000)

expect(code).to_equal(1)
expect(stdout).to_contain("preflight-scan device=" + fake_dev + " status=failed")
expect(stdout).to_contain("no distinct assignable user namespace")
expect(stderr).to_contain("preflight-scan=not-ready matched_devices=1 ready_devices=0")
expect(report_text).to_contain("physical_nvme_preflight_scan:")
expect(report_text).to_contain("device: " + fake_dev)
expect(report_text).to_contain("status: failed")
expect(report_text).to_contain("reason: [physical-nvme] no distinct assignable user namespace found for " + fake_dev)
expect(report_text).to_contain("accepted: false")
expect(report_text).to_contain("status: not-ready")
expect(report_text).to_contain("matched_devices: 1")
expect(report_text).to_contain("ready_devices: 0")
expect(preflight_probe_code).to_equal(0)
```

</details>

#### rejects preflight scan when report output already exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_scan_existing_report_sysfs"
val fake_dir = "/tmp/simpleos_nvme_preflight_scan_existing_report_device"
val fake_dev = fake_dir + "/nvme8n1"
val fake_sysfs = fake_root + "/nvme8n1"
val report = "/tmp/simpleos_nvme_preflight_scan_existing_report.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dir + "\" \"" + report + "\" \"" + report + ".tmp.\"* && mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_dir + "\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SNEXISTS\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(report, "existing scan report\n")).to_equal(true)

val (_stdout, stderr, code) = _run_lab_preflight_scan_report_with_sysfs(fake_dev, fake_root, report)
val report_text = rt_file_read_text(report) ?? ""

expect(code).to_equal(2)
expect(stderr).to_contain("preflight scan report already exists")
expect(report_text).to_equal("existing scan report\n")
```

</details>

#### rejects preflight scan when scan report and selected preflight output paths match

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_scan_same_output_sysfs"
val fake_dir = "/tmp/simpleos_nvme_preflight_scan_same_output_device"
val fake_dev = fake_dir + "/nvme8n1"
val fake_sysfs = fake_root + "/nvme8n1"
val output = "/tmp/simpleos_nvme_preflight_scan_same_output.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dir + "\" \"" + output + "\" \"" + output + ".tmp.\"* && mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_dir + "\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SNSAMEOUT\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)

val (_stdout, stderr, code) = _run_lab_preflight_scan_report_and_preflight_with_sysfs(fake_dev, fake_root, output, output)
val output_text = rt_file_read_text(output) ?? ""

expect(code).to_equal(2)
expect(stderr).to_contain("--preflight-scan report outputs must differ")
expect(output_text).to_equal("")
```

</details>

#### rejects standalone preflight when output reports would be overwritten

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_nvme = "/tmp/simpleos_nvme_preflight_existing_output_device"
val report = "/tmp/simpleos_nvme_preflight_existing_report.sdn"
val preflight_out = "/tmp/simpleos_nvme_preflight_existing_out.sdn"
val _ = rt_file_delete(fake_nvme)
val _report_cleanup = rt_file_delete(report)
val _preflight_cleanup = rt_file_delete(preflight_out)
expect(rt_file_write_text(fake_nvme, "device")).to_equal(true)

val (_same_stdout, same_stderr, same_code) = _run_lab_preflight_with_two_outputs(fake_nvme, report, report)
expect(same_code).to_equal(2)
expect(same_stderr).to_contain("--preflight report outputs must differ")

expect(rt_file_write_text(report, "old report\n")).to_equal(true)
val (_report_stdout, report_stderr, report_code) = _run_lab_preflight_with_two_outputs(fake_nvme, report, preflight_out)
expect(report_code).to_equal(2)
expect(report_stderr).to_contain("preflight report already exists")
val _report_delete = rt_file_delete(report)

expect(rt_file_write_text(preflight_out, "old preflight\n")).to_equal(true)
val (_preflight_stdout, preflight_stderr, preflight_code) = _run_lab_preflight_with_two_outputs(fake_nvme, report, preflight_out)
expect(preflight_code).to_equal(2)
expect(preflight_stderr).to_contain("preflight output already exists")
```

</details>

#### writes physical NVMe preflight identity for lab comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_sysfs"
val fake_dev = "/tmp/simpleos_nvme_preflight_device_identity/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val fake_user_sysfs = fake_root + "/nvme9n2"
val report = "/tmp/simpleos_nvme_preflight_identity.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + report + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_user_sysfs + "/device\" \"" + fake_dev + "\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/nsid", "2\n")).to_equal(true)

val (_stdout, _stderr, code) = _run_lab_preflight_with_report(fake_dev, fake_root, report)
val report_text = rt_file_read_text(report) ?? ""

expect(code).to_equal(0)
expect(report_text).to_contain("physical_nvme_preflight:")
expect(report_text).to_contain("nvme_device_glob: " + fake_dev)
expect(report_text).to_contain("checker: ")
expect(report_text).to_contain("controller: nvme9")
expect(report_text).to_contain("model: Samsung PM9A3")
expect(report_text).to_contain("serial: SN123456")
expect(report_text).to_contain("namespace_nsid: 1")
expect(report_text).to_contain("user_namespace_device: " + "/tmp/simpleos_nvme_preflight_device_identity/nvme9n2")
expect(report_text).to_contain("user_namespace_controller: nvme9")
expect(report_text).to_contain("user_namespace_model: Samsung PM9A3")
expect(report_text).to_contain("user_namespace_serial: SN123456")
expect(report_text).to_contain("user_namespace_nsid: 2")
expect(report_text).to_contain("user_namespace_same_controller: true")
expect(report_text).to_contain("same_physical_device: true")
```

</details>

#### rejects physical NVMe preflight when user namespace identity differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_root = "/tmp/simpleos_nvme_preflight_user_identity_mismatch_sysfs"
val fake_dev = "/tmp/simpleos_nvme_preflight_user_identity_mismatch_device/nvme9n1"
val fake_sysfs = fake_root + "/nvme9n1"
val fake_user_sysfs = fake_root + "/nvme9n2"
val report = "/tmp/simpleos_nvme_preflight_user_identity_mismatch.sdn"
val _cleanup = rt_process_run_timeout("/bin/sh", ["-c", "rm -rf \"" + fake_root + "\" \"" + fake_dev + "\" \"" + report + "\""], 5000)
val _mkdir = rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p \"" + fake_sysfs + "/device\" \"" + fake_user_sysfs + "/device\" \"" + fake_dev + "\""], 5000)
expect(rt_file_write_text(fake_dev, "device")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/model", "Samsung PM9A3\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_sysfs + "/nsid", "1\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/model", "DIFFERENT\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/device/serial", "SN123456\n")).to_equal(true)
expect(rt_file_write_text(fake_user_sysfs + "/nsid", "2\n")).to_equal(true)

val (_stdout, stderr, code) = _run_lab_preflight_with_report(fake_dev, fake_root, report)

expect(code).to_equal(1)
expect(stderr).to_contain("user namespace identity does not match system namespace controller")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simpleos_nvme_serial_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS physical NVMe serial checker app

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
