# Arm64 Wm Qemu Contract Specification

> Tests covering ARM64 SimpleOS WM QEMU contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Wm Qemu Contract Specification

## Scenarios

### ARM64 SimpleOS WM QEMU contract

#### keeps the guide bound to the canonical ARM64 desktop entry and ramfb target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the guide bound to the canonical ARM64 desktop entry and ramfb target
   - Expected: file_exists(_guide_path()) is true
   - Expected: file_exists(_entry_path()) is true
   - Expected: file_exists(_ramfb_path()) is true
   - Expected: file_exists(_console_path()) is true
   - Expected: guide does not contain `examples/09_embedded/simple_os/arch/arm64/wm_entry.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the guide bound to the canonical ARM64 desktop entry and ramfb target")
expect(file_exists(_guide_path())).to_equal(true)
expect(file_exists(_entry_path())).to_equal(true)
expect(file_exists(_ramfb_path())).to_equal(true)
expect(file_exists(_console_path())).to_equal(true)
val guide = file_read_text(_guide_path())
expect(guide).to_contain("examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl")
expect(guide.contains("examples/09_embedded/simple_os/arch/arm64/wm_entry.spl")).to_equal(false)
expect(guide).to_contain("--target aarch64-unknown-none")
expect(guide).to_contain("qemu-system-aarch64")
expect(guide).to_contain("-machine virt")
expect(guide).to_contain("-serial file:build/os/arm64_wm_serial.log")
expect(guide).to_contain("-kernel build/os/simpleos_arm64_wm.elf")
expect(guide).to_contain("-device ramfb")
expect(guide).to_contain("build/os/simpleos_arm64_wm.elf")
expect(guide).to_contain("bin/simple os build --scenario=arm64-wm-ramfb")
expect(guide).to_contain("bin/simple os run --scenario=arm64-wm-ramfb")
expect(guide).to_contain("bin/simple os test --scenario=arm64-wm-ramfb")
```

</details>

#### keeps documented serial markers present in the ARM64 WM source

- keeps documented serial markers present in the ARM64 WM source
   - Expected: entry does not contain `[WM] Glass desktop rendered!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps documented serial markers present in the ARM64 WM source")
val guide = file_read_text(_guide_path())
val entry = file_read_text(_entry_path())
val ramfb = file_read_text(_ramfb_path())
expect(guide).to_contain("[desktop-gui-arm64] boot")
expect(guide).to_contain("[WM] fw_cfg sig: 81 69 77 85")
expect(guide).to_contain("[WM] Found etc/ramfb in fw_cfg")
expect(guide).to_contain("[WM] ramfb configured successfully via fw_cfg DMA")
expect(guide).to_contain("[desktop-gui-arm64] desktop-ready revision=")
expect(entry).to_contain("[desktop-gui-arm64] boot")
expect(entry).to_contain("[desktop-gui-arm64] desktop-ready revision=")
expect(entry.contains("[WM] Glass desktop rendered!")).to_equal(false)
expect(ramfb).to_contain("[WM] fw_cfg sig:")
expect(ramfb).to_contain("[WM] Found etc/ramfb in fw_cfg")
expect(ramfb).to_contain("[WM] ramfb configured successfully via fw_cfg DMA")
```

</details>

#### documents the platform-specific adapter boundary and canonical Engine2D executor

- documents the platform-specific adapter boundary and canonical Engine2D executor
   - Expected: entry does not contain `wm_entry_io`
   - Expected: entry does not contain `extern fn rt_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents the platform-specific adapter boundary and canonical Engine2D executor")
val entry = file_read_text(_entry_path())
val ramfb = file_read_text(_ramfb_path())
val console = file_read_text(_console_path())
expect(entry).to_contain("Canonical ARM64 production desktop entry for QEMU virt ramfb")
expect(entry).to_contain("FramebufferDriver.from_scanout_raw(")
expect(entry).to_contain("Engine2dWmFrameExecutor.create(")
expect(entry).to_contain("uart_data_ready()")
expect(entry).to_contain("uart_read_char()")
expect(entry.contains("wm_entry_io")).to_equal(false)
expect(entry.contains("extern fn rt_")).to_equal(false)
expect(ramfb).to_contain("_FW_CFG_BASE: u64 = 0x09020000")
expect(ramfb).to_contain("etc/ramfb")
expect(ramfb).to_contain("mmio_memory_barrier()")
expect(console).to_contain("pl011_data_ready")
```

</details>

#### has a host readiness probe for the live ARM64 QEMU ramfb lane

- has a host readiness probe for the live ARM64 QEMU ramfb lane
   - Expected: file_exists(_readiness_script_path()) is true
   - Expected: result[2] equals `0`
   - Expected: result[0] contains `"cpu: host") or result[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a host readiness probe for the live ARM64 QEMU ramfb lane")
val guide = file_read_text(_guide_path())
expect(file_exists(_readiness_script_path())).to_equal(true)
expect(guide).to_contain("scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs")
val result = process_run_timeout("sh", [_readiness_script_path()], 10000)
if result[2] != 0:
    print "[arm64_wm_qemu_contract_spec] readiness probe failed:\n{result[0]}{result[1]}"
expect(result[2]).to_equal(0)
expect(result[0]).to_contain("arm64_wm_qemu_readiness: ready")
expect(result[0]).to_contain("qemu_system: qemu-system-aarch64")
expect(result[0]).to_contain("machine_virt: true")
expect(result[0]).to_contain("ramfb_device: true")
expect(result[0]).to_contain("dry_run_parse: true")
expect(result[0].contains("accelerator: hvf") or result[0].contains("accelerator: kvm") or
    result[0].contains("accelerator: tcg")).to_equal(true)
expect(result[0].contains("cpu: host") or result[0].contains("cpu: cortex-a57")).to_equal(true)
```

</details>

#### keeps the runner portable across Darwin and Linux hosts

- keeps the runner portable across Darwin and Linux hosts
   - Expected: arm64_wm_qemu_cpu_for_host("macos", "aarch64") equals `host`
   - Expected: arm64_wm_qemu_cpu_for_host("linux", "x86_64") equals `cortex-a57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the runner portable across Darwin and Linux hosts")
expect(arm64_wm_qemu_cpu_for_host("macos", "aarch64")).to_equal("host")
expect(arm64_wm_qemu_extra_for_host("macos", "aarch64")).to_contain("hvf")
expect(arm64_wm_qemu_cpu_for_host("linux", "x86_64")).to_equal("cortex-a57")
expect(arm64_wm_qemu_extra_for_host("linux", "x86_64")).to_contain("tcg")
```

</details>

#### defines a host-runnable ARM64 WM QEMU target and launch command

- defines a host-runnable ARM64 WM QEMU target and launch command


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines a host-runnable ARM64 WM QEMU target and launch command")
val target = get_arm64_wm_qemu_target()
val build_args = os_native_build_args(target, "llvm")
expect(build_args).to_contain("examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl")
expect(build_args).to_contain("aarch64-unknown-none")
expect(build_args).to_contain("examples/09_embedded/simple_os/arch/arm64/linker.ld")
expect(build_args).to_contain("build/os/simpleos_arm64_wm.elf")
expect(build_args).to_contain("--entry-closure")
expect(build_args).to_contain("--timeout")
expect(build_args).to_contain("180")

val qemu_args = build_qemu_command(target)
expect(qemu_args).to_contain("qemu-system-aarch64")
expect(qemu_args).to_contain("-machine")
expect(qemu_args).to_contain("virt")
expect(qemu_args).to_contain("-accel")
expect(qemu_args).to_contain(target.qemu_extra[1])
expect(qemu_args).to_contain("-cpu")
expect(qemu_args).to_contain(target.qemu_cpu)
expect(qemu_args).to_contain("-kernel")
expect(qemu_args).to_contain("build/os/simpleos_arm64_wm.elf")
expect(qemu_args).to_contain("-device")
expect(qemu_args).to_contain("ramfb")
expect(qemu_args).to_contain("-display")
expect(qemu_args).to_contain("none")
expect(qemu_args).to_contain("-serial")
expect(qemu_args).to_contain("stdio")
```

</details>

#### exposes the ARM64 WM ramfb lane as a named QEMU scenario

- exposes the ARM64 WM ramfb lane as a named QEMU scenario
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl`
   - Expected: target.output equals `build/os/simpleos_arm64_wm.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes the ARM64 WM ramfb lane as a named QEMU scenario")
val scenario_opt = get_scenario("arm64-wm-ramfb")
assert_not_equal(scenario_opt, nil)
if scenario_opt == nil:
    return
val scenario = scenario_opt
val target = scenario_target(scenario)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl")
expect(target.output).to_equal("build/os/simpleos_arm64_wm.elf")
val cmd = build_scenario_command(scenario, target.output)
expect(cmd).to_contain("qemu-system-aarch64")
expect(cmd).to_contain("-machine")
expect(cmd).to_contain("virt")
expect(cmd).to_contain("-cpu")
expect(cmd).to_contain(target.qemu_cpu)
expect(cmd).to_contain("-accel")
expect(cmd).to_contain(target.qemu_extra[1])
expect(cmd).to_contain("-m")
expect(cmd).to_contain("384M")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_arm64_wm.elf")
expect(cmd).to_contain("-device")
expect(cmd).to_contain("ramfb")
```

</details>

#### uses documented ARM64 WM markers for scenario acceptance

- uses documented ARM64 WM markers for scenario acceptance
   - Expected: qemu_scenario_serial_acceptance_reason(scenario, "", complete) equals `ready`
   - Expected: qemu_scenario_serial_acceptance_reason(scenario, "off", complete) equals `ready`
   - Expected: scenario_test_timeout_ms(scenario) equals `120000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses documented ARM64 WM markers for scenario acceptance")
val scenario_opt = get_scenario("arm64-wm-ramfb")
assert_not_equal(scenario_opt, nil)
if scenario_opt == nil:
    return
val scenario = scenario_opt
val complete = _complete_arm64_wm_serial()
expect(qemu_scenario_serial_acceptance_reason(scenario, "", complete)).to_equal("ready")
expect(qemu_scenario_serial_acceptance_reason(scenario, "off", complete)).to_equal("ready")
val missing_ramfb = "[desktop-gui-arm64] boot\n" +
    "[WM] fw_cfg sig: 81 69 77 85\n" +
    "[WM] Found etc/ramfb in fw_cfg\n" +
    "[desktop-gui-arm64] desktop-ready revision=1\n"
expect(qemu_scenario_serial_acceptance_reason(scenario, "", missing_ramfb)).to_equal(
    "missing-marker:[WM] ramfb configured successfully via fw_cfg DMA"
)
expect(scenario_test_timeout_ms(scenario)).to_equal(120000)
```

</details>

#### keeps SimpleOS CLI scenario dispatch wired to the ARM64 WM scenario

- keeps SimpleOS CLI scenario dispatch wired to the ARM64 WM scenario


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps SimpleOS CLI scenario dispatch wired to the ARM64 WM scenario")
val cli = file_read_text(_cli_path())
expect(cli).to_contain("os_parse_scenario_arg(args)")
expect(cli).to_contain("get_scenario(scenario_name)")
expect(cli).to_contain("val ok = build_scenario(scenario)")
expect(cli).to_contain("val built = build_scenario(scenario)")
expect(cli).to_contain("val ok = run_scenario(scenario)")
expect(cli).to_contain("val ok = test_scenario(scenario, scenario_test_timeout_ms(scenario))")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/arm64_wm_qemu_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 SimpleOS WM QEMU contract.
- ARM64 SimpleOS WM QEMU contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c9379de0678abdcaf3e604cf8e0647aab9be050a908cfea17ba3ec86b0aedca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c9379de0678abdcaf3e604cf8e0647aab9be050a908cfea17ba3ec86b0aedca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c9379de0678abdcaf3e604cf8e0647aab9be050a908cfea17ba3ec86b0aedca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gui/arm64_wm_qemu_contract_spec.spl
mirror: doc/06_spec/03_system/gui/arm64_wm_qemu_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/arm64_wm_qemu_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/arm64_wm_qemu_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/arm64_wm_qemu_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/arm64_wm_qemu_contract_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the guide bound to the canonical ARM64 desktop entry and ramfb target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/arm64_wm_qemu_contract_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps documented serial markers present in the ARM64 WM source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/arm64_wm_qemu_contract_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the platform-specific adapter boundary and canonical Engine2D executor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
