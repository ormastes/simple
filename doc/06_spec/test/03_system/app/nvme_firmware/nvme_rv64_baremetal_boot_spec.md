# nvme_rv64_baremetal_boot_spec

> NVMe firmware RV64 baremetal boot evidence.

<!-- sdn-diagram:id=nvme_rv64_baremetal_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_rv64_baremetal_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_rv64_baremetal_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_rv64_baremetal_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_rv64_baremetal_boot_spec

NVMe firmware RV64 baremetal boot evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/nvme_rv64_baremetal_boot_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware RV64 baremetal boot evidence.

The real boot scenario is fail-closed: it passes only when the prebuilt RV64
firmware ELF boots under QEMU and prints every required serial marker. The
wrapper self-test separately proves fake-QEMU missing-marker, empty-serial, and
serial-FAIL cases are rejected.

## Scenarios

### NVMe firmware rv64 baremetal wrapper

#### has an explicit RV64 firmware ELF build recipe

- The RV64 direct firmware build script is shell-parseable
   - Expected: code equals `0`
   - Expected: elapsed_code equals `0`
   - Expected: reason_code equals `0`
   - Expected: duplicate_main_code equals `0`
   - Expected: heartbeat_code equals `0`
   - Expected: background_code equals `0`
   - Expected: stopped_code equals `0`
   - Expected: closure_code equals `0`
   - Expected: stub_code equals `0`
   - Expected: cache_code equals `0`
   - Expected: failure_focus_code equals `0`
   - Expected: section_code equals `0`
   - Expected: task_pool_code equals `0`
   - Expected: section_path_code equals `0`
   - Expected: empty_serial_code equals `0`
   - Expected: entry_marker_code equals `0`
   - Expected: opensbi_code equals `0`
   - Expected: log_code equals `0`
- The RV64 boot wrapper tells operators how to create missing boot media


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The RV64 direct firmware build script is shell-parseable")
val (out, err, code) = _run("sh -n examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(code).to_equal(0)
val (elapsed_out, elapsed_err, elapsed_code) = _run("rg -n 'NVME_RV64_BUILD_FAILED.*elapsed=|NVME_RV64_NATIVE_BUILD_DONE elapsed=' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(elapsed_code).to_equal(0)
val (reason_out, reason_err, reason_code) = _run("rg -n 'external-termination-before-timeout|native-build-timeout' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(reason_code).to_equal(0)
val (duplicate_main_out, duplicate_main_err, duplicate_main_code) = _run("rg -n 'native-build-duplicate-symbol|native-build-duplicate-main|duplicate symbol:' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(duplicate_main_code).to_equal(0)
val (heartbeat_out, heartbeat_err, heartbeat_code) = _run("rg -n 'NVME_RV64_BUILD_HEARTBEAT elapsed=' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(heartbeat_code).to_equal(0)
val (background_out, background_err, background_code) = _run("rg -n 'NVME_RV64_BUILD_BACKGROUND|NVME_RV64_BUILD_STATUS' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(background_code).to_equal(0)
val (stopped_out, stopped_err, stopped_code) = _run("rg -n 'NVME_RV64_BUILD_STATUS stopped|NVME_RV64_BUILD_STATUS running|bg_out=\\$BG_OUT_LOG|bg_err=\\$BG_ERR_LOG|LAST_PHASE|LAST_DONE|LAST_HEARTBEAT|last_heartbeat=|last_done=|last_phase=' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(stopped_code).to_equal(0)
val (closure_out, closure_err, closure_code) = _run("rg -n 'closure=compiler-verbose|--verbose' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(closure_code).to_equal(0)
val (stub_out, stub_err, stub_code) = _run("rg -n 'SIMPLE_NO_STUB_FALLBACK=1|stub_fallback=disabled' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(stub_code).to_equal(0)
val (cache_out, cache_err, cache_code) = _run("rg -n 'cache_dir=\\$CACHE_DIR|--cache-dir \"\\$CACHE_DIR\"|nvme_fw_rv64_\\$\\{SECTION\\}' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(cache_code).to_equal(0)
val (failure_focus_out, failure_focus_err, failure_focus_code) = _run("rg -n 'Entry closure files|Driver start|phase2:parse:file:|\"\\$OUT_LOG\" \"\\$ERR_LOG\"' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(failure_focus_code).to_equal(0)
val (section_out, section_err, section_code) = _run("rg -n 'NVME_RV64_BUILD_SECTION|section=\\$SECTION|invalid-section|logic_sections_primary|logic_sections_secondary|logic_target|target_logic|target_core|rt_rv64_boot_optional_nvme_fw_selftest' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(section_code).to_equal(0)
val (task_pool_out, task_pool_err, task_pool_code) = _run("rg -n 'task-pool fail-closed floor|pool_closed_status.*130' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(task_pool_code).to_equal(0)
val (section_out_path, section_err_path, section_path_code) = _run("rg -n 'nvme_fw_rv64_\\$\\{SECTION\\}\\.elf|nvme_fw_rv64_\\$\\{SECTION\\}\\.o' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(section_path_code).to_equal(0)
val (empty_serial_out, empty_serial_err, empty_serial_code) = _run("rg -n 'NVME_RV64_FAKE_SERIAL=empty|RESULT: FAIL \\(serial empty\\)|\\[ ! -s \"\\$LOG\" \\]' examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs")
expect(empty_serial_code).to_equal(0)
val (entry_marker_out, entry_marker_err, entry_marker_code) = _run("rg -n 'RV64 ENTRY|putc 69' examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(entry_marker_code).to_equal(0)
val (opensbi_out, opensbi_err, opensbi_code) = _run("rg -n 'OpenSBI S-mode payload' examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs && ! rg -n -- '-bios none' examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs")
expect(opensbi_code).to_equal(0)
val (log_out, log_err, log_code) = _run("rg -n 'NVME_RV64_BOOT_LOG|PRINT_LOG=\"\\$\\{LOG\\}\\.print\"' examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs")
expect(log_code).to_equal(0)

step("The RV64 boot wrapper tells operators how to create missing boot media")
val (hint_out, hint_err, hint_code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs")
expect(hint_out).to_contain("missing-media: build/nvme_fw_rv64.elf")
expect(hint_out).to_contain("fw_rv64/build.shs")
```

</details>

#### boots the RV64 NVMe firmware ELF on QEMU and reports subsystem health

- Run boot.shs for the RV64 NVMe firmware wrapper against the real ELF
- The serial console shows the RV64 boot and firmware PASS markers
- verdict = "missing-media: build/nvme fw rv64 elf not built
   - Expected: verdict equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run boot.shs for the RV64 NVMe firmware wrapper against the real ELF")
val (out, err, code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs")

step("The serial console shows the RV64 boot and firmware PASS markers")
var verdict: text = "pass"
if out.contains("missing-media:"):
    verdict = "missing-media: build/nvme_fw_rv64.elf not built (run fw_rv64/build.shs)"
else:
    if not out.contains("SimpleOS RV64"):
        verdict = "boot-fail: SimpleOS RV64 banner absent"
    else:
        if not out.contains("[BOOT] boot complete"):
            verdict = "boot-fail: boot-complete marker absent"
        else:
            if not out.contains("ALL RV64 NVME FW CHECKS PASS"):
                verdict = "boot-fail: firmware PASS marker absent"
            else:
                if not out.contains("RESULT: PASS"):
                    verdict = "boot-fail: wrapper pass marker absent"
                else:
                    if out.contains("FAIL"):
                        verdict = "boot-fail: serial failure marker present"
expect(verdict).to_equal("pass")
```

</details>

#### boots the RV64 target-core firmware probe on QEMU

- Build the small target-core RV64 probe
   - Expected: build_code equals `0`
- Boot the target-core probe through OpenSBI and require the firmware PASS marker
   - Expected: boot_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the small target-core RV64 probe")
val (build_out, build_err, build_code) = _run("NVME_RV64_BUILD_SECTION=target_core NVME_RV64_BUILD_TIMEOUT_SECS=90 sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(build_code).to_equal(0)
expect(build_out).to_contain("build/nvme_fw_rv64_target_core.elf")

step("Boot the target-core probe through OpenSBI and require the firmware PASS marker")
val (boot_out, boot_err, boot_code) = _run("NVME_RV64_BOOT_LOG=build/nvme_fw_rv64_target_core_spec_serial.log sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs build/nvme_fw_rv64_target_core.elf")
expect(boot_code).to_equal(0)
expect(boot_out).to_contain("RV64 ENTRY")
expect(boot_out).to_contain("ALL RV64 NVME FW CHECKS PASS")
expect(boot_out).to_contain("RESULT: PASS")
```

</details>

#### boots the RV64 target logic firmware probe on QEMU

- Build the target profile/aperture RV64 probe
   - Expected: build_code equals `0`
- Boot the target logic probe through OpenSBI and require the firmware PASS marker
   - Expected: boot_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the target profile/aperture RV64 probe")
val (build_out, build_err, build_code) = _run("NVME_RV64_BUILD_SECTION=target_logic NVME_RV64_BUILD_TIMEOUT_SECS=90 sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs")
expect(build_code).to_equal(0)
expect(build_out).to_contain("build/nvme_fw_rv64_target_logic.elf")

step("Boot the target logic probe through OpenSBI and require the firmware PASS marker")
val (boot_out, boot_err, boot_code) = _run("NVME_RV64_BOOT_LOG=build/nvme_fw_rv64_target_logic_spec_serial.log sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs build/nvme_fw_rv64_target_logic.elf")
expect(boot_code).to_equal(0)
expect(boot_out).to_contain("RV64 ENTRY")
expect(boot_out).to_contain("ALL RV64 NVME FW CHECKS PASS")
expect(boot_out).to_contain("RESULT: PASS")
```

</details>

#### runs the rv64 boot wrapper fail-closed self-test

- Run boot.shs --self-test for the RV64 NVMe firmware wrapper
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run boot.shs --self-test for the RV64 NVMe firmware wrapper")
val (out, err, code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs --self-test")
expect(code).to_equal(0)
expect(out).to_contain("STATUS: PASS nvme-rv64-boot self-test")
_expect_no_fail_marker(out, "rv64 boot wrapper self-test")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
