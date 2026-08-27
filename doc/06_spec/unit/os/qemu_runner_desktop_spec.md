# Qemu Runner Desktop Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Desktop Specification

## Scenarios

#### builds a desktop UEFI validator command requiring structured FAT checks for migrated tool apps

- builds a desktop UEFI validator command requiring structured FAT checks for migrated tool apps


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a desktop UEFI validator command requiring structured FAT checks for migrated tool apps")
val cmd = desktop_uefi_disk_image_tool_app_validation_command("build/os/fat32-x86_64.img")
expect(cmd).to_contain("command -v mdir")
expect(cmd).to_contain("::/SYS/APPS/simple_browser")
expect(cmd).to_contain("::/SYS/APPS/simple_browser.smf")
expect(cmd).to_contain("::/SYS/APPS/simple_compiler")
expect(cmd).to_contain("::/SYS/APPS/simple_compiler.smf")
expect(cmd).to_contain("::/SYS/APPS/simple_interpreter")
expect(cmd).to_contain("::/SYS/APPS/simple_interpreter.smf")
expect(cmd).to_contain("::/SYS/APPS/simple_loader")
expect(cmd).to_contain("::/SYS/APPS/simple_loader.smf")
expect(cmd).to_contain("::/SYS/APPS/simple")
expect(cmd).to_contain("::/SYS/APPS/simple.smf")
expect(cmd).to_contain("::/SYS/APPS/llvm")
expect(cmd).to_contain("::/SYS/APPS/llvm.smf")
expect(cmd).to_contain("::/SYS/APPS/rust")
expect(cmd).to_contain("::/SYS/APPS/rust.smf")
expect(cmd).to_contain("::/SYS/LLVMVER.TXT")
expect(cmd).to_contain("::/SYS/RUSTVER.TXT")
expect(cmd).to_contain("mdir required; raw-image scan is diagnostic-only")
expect(cmd).to_contain("command -v mtype")
expect(cmd).to_contain("/sys/apps/simple_browser")
expect(cmd).to_contain("/sys/apps/simple_compiler")
expect(cmd).to_contain("/sys/apps/simple_interpreter")
expect(cmd).to_contain("/sys/apps/simple_loader")
expect(cmd).to_contain("/sys/apps/simple")
expect(cmd).to_contain("/sys/apps/llvm")
expect(cmd).to_contain("/sys/apps/rust")
expect(cmd).to_contain("grep -q '^SimpleOS LLVM standalone app v1'")
expect(cmd).to_contain("grep -q '^SimpleOS Rust standalone app v1'")
expect(cmd).to_contain("grep -q 'mode=native-filesystem-app'")
expect(cmd).to_contain("grep -q 'status=standalone-required'")
expect(cmd).to_contain("/usr/share/simpleos/toolchain/llvm/hello.ll")
expect(cmd).to_contain("/usr/share/simpleos/toolchain/rust/hello.rs")
```

</details>

#### defines a BGA WM Simple Web Engine2D scenario

- defines a BGA WM Simple Web Engine2D scenario
   - Expected: scenario.name equals `x64-wm-simple-web-check`
   - Expected: scenario.arch equals `Architecture.X86_64`
   - Expected: scenario.memory equals `2G`
   - Expected: scenario.qemu_extra does not contain `virtio-gpu,disable-modern=on,disable-legacy=off`
   - Expected: scenario_test_timeout_ms(scenario) equals `120000`
   - Expected: scenario_name_or_missing("x64-wm-simple-web-check") equals `x64-wm-simple-web-check`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
   - Expected: target.output equals `build/os/simpleos_wm_simple_web_check_32.elf`
   - Expected: target.qemu_memory equals `2G`
   - Expected: target.qemu_cpu equals `max`
   - Expected: direct_target.entry equals `target.entry`
   - Expected: cmd[0] equals `qemu-system-x86_64`
   - Expected: cmd does not contain `virtio-gpu,disable-modern=on,disable-legacy=off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines a BGA WM Simple Web Engine2D scenario")
val scenario = scenario_x64_wm_simple_web_check()
expect(scenario.name).to_equal("x64-wm-simple-web-check")
expect(scenario.arch).to_equal(Architecture.X86_64)
expect(scenario.memory).to_equal("2G")
expect(scenario.qemu_extra).to_contain("-vga")
expect(scenario.qemu_extra).to_contain("std")
expect(scenario.qemu_extra.contains("virtio-gpu,disable-modern=on,disable-legacy=off")).to_equal(false)
expect(scenario_test_timeout_ms(scenario)).to_equal(120000)

expect(scenario_name_or_missing("x64-wm-simple-web-check")).to_equal("x64-wm-simple-web-check")
val target = scenario_target(scenario)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl")
expect(target.output).to_equal("build/os/simpleos_wm_simple_web_check_32.elf")
expect(target.qemu_memory).to_equal("2G")
expect(target.qemu_cpu).to_equal("max")

val direct_target = get_wm_simple_web_check_target()
expect(direct_target.entry).to_equal(target.entry)

val cmd = build_scenario_command(scenario, target.output)
expect(cmd[0]).to_equal("qemu-system-x86_64")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_wm_simple_web_check_32.elf")
expect(cmd).to_contain("-vga")
expect(cmd).to_contain("std")
expect(cmd.contains("virtio-gpu,disable-modern=on,disable-legacy=off")).to_equal(false)
```

</details>

#### requires WM Simple Web render markers instead of a bare TEST PASSED

- requires WM Simple Web render markers instead of a bare TEST PASSED
   - Expected: wm_simple_web_serial_accepts_completion(complete) is true
   - Expected: wm_simple_web_serial_acceptance_reason(bare_pass) equals `missing-marker:[GUI] mmio-probe-painted`
   - Expected: wm_simple_web_serial_acceptance_reason(missing_taskbar) equals `missing-marker:[mdi-demo] taskbar-ready`
   - Expected: qemu_scenario_serial_acceptance_reason(scenario, "", complete) equals `ready`
   - Expected: qemu_scenario_serial_acceptance_reason(scenario, "", bare_pass) equals `missing-marker:[GUI] mmio-probe-painted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires WM Simple Web render markers instead of a bare TEST PASSED")
val scenario = scenario_x64_wm_simple_web_check()
val complete = wm_simple_web_required_marker_fragments().join("\n")
val bare_pass = "boot ok\nTEST PASSED\n"
val missing_taskbar = "[GUI] mmio-probe-painted\n" +
    "[wm-demo] wm-service-ready\n" +
    "[e2d-demo] engine-core-ready\n" +
    "[web-demo] pixels-ready expected=42\n" +
    "[mdi-demo] windows-ready count=3\n" +
    "[mdi-demo] top-command-lane-ready\n" +
    "[mdi-demo] html-renderable window=browser pixels=42\n" +
    "[integrated-demo] render-ready\n" +
    "TEST PASSED\n"

expect(wm_simple_web_serial_accepts_completion(complete)).to_equal(true)
expect(wm_simple_web_serial_acceptance_reason(bare_pass)).to_equal("missing-marker:[GUI] mmio-probe-painted")
expect(wm_simple_web_serial_acceptance_reason(missing_taskbar)).to_equal("missing-marker:[mdi-demo] taskbar-ready")
expect(qemu_scenario_serial_acceptance_reason(scenario, "", complete)).to_equal("ready")
expect(qemu_scenario_serial_acceptance_reason(scenario, "", bare_pass)).to_equal("missing-marker:[GUI] mmio-probe-painted")
```

</details>

#### keeps headless targets on stdio and disables the display

- keeps headless targets on stdio and disables the display


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps headless targets on stdio and disables the display")
val target = get_target(Architecture.X86_64)
val cmd = build_qemu_command(target)
expect(cmd).to_contain("-no-user-config")
expect(cmd).to_contain("-monitor")
expect(cmd).to_contain("none")
expect(cmd).to_contain("-net")
expect(cmd).to_contain("-serial")
expect(cmd).to_contain("stdio")
expect(cmd).to_contain("-display")
expect(cmd).to_contain("none")
```

</details>

#### hardens x86_64 scenario launches without disabling explicit network scenarios

- hardens x86_64 scenario launches without disabling explicit network scenarios
   - Expected: "missing" equals `x64-desktop-test`
   - Expected: net_cmd does not contain `-net`
   - Expected: scenario_name_or_missing("x64-ssh") equals `x64-ssh`
   - Expected: ssh_cmd does not contain `-net`
   - Expected: scenario_test_timeout_ms(ssh) equals `120000`
   - Expected: ssh_target.entry equals `get_ssh_live_target().entry`
   - Expected: ssh_target.output equals `build/os/simpleos_ssh_live_32.elf`
   - Expected: ssh_probe_target.entry equals `examples/09_embedded/simple_os/arch/x86_64/ssh_x25519_probe_entry.spl`
   - Expected: ssh_probe_target.output equals `build/os/simpleos_ssh_x25519_probe_32.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hardens x86_64 scenario launches without disabling explicit network scenarios")
val desktop = get_scenario("x64-desktop-test")
if val resolved_desktop = desktop:
    val desktop_cmd = build_scenario_command(resolved_desktop, "build/os/simpleos_desktop_e2e_32.elf")
    expect(desktop_cmd).to_contain("-no-user-config")
    expect(desktop_cmd).to_contain("-monitor")
    expect(desktop_cmd).to_contain("-net")
    expect(desktop_cmd).to_contain("none")
else:
    expect("missing").to_equal("x64-desktop-test")

val net_user = scenario_x64_net_user()
val net_cmd = build_scenario_command(net_user, "build/os/simpleos_x86_64.elf")
expect(net_cmd).to_contain("-no-user-config")
expect(net_cmd).to_contain("-monitor")
expect(net_cmd).to_contain("-netdev")
expect(net_cmd.contains("-net")).to_equal(false)

val ssh = scenario_x64_ssh()
expect(scenario_name_or_missing("x64-ssh")).to_equal("x64-ssh")
val ssh_cmd = build_scenario_command(ssh, "build/os/simpleos_x86_64.elf")
expect(ssh_cmd).to_contain("user,id=n0,hostfwd=tcp::2222-:22")
expect(ssh_cmd.contains("-net")).to_equal(false)
expect(scenario_test_timeout_ms(ssh)).to_equal(120000)
val ssh_target = scenario_target(ssh)
expect(ssh_target.entry).to_equal(get_ssh_live_target().entry)
expect(ssh_target.output).to_equal("build/os/simpleos_ssh_live_32.elf")

val ssh_probe_target = get_ssh_x25519_probe_target()
expect(ssh_probe_target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/ssh_x25519_probe_entry.spl")
expect(ssh_probe_target.output).to_equal("build/os/simpleos_ssh_x25519_probe_32.elf")
```

</details>

#### keeps gui targets quiet by default

- keeps gui targets quiet by default
   - Expected: cmd does not contain `stdio`
   - Expected: cmd does not contain `-display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps gui targets quiet by default")
val target = get_gui_target()
val cmd = build_qemu_command(target)
expect(cmd).to_contain("-no-user-config")
expect(cmd).to_contain("-monitor")
expect(cmd).to_contain("-net")
expect(cmd).to_contain("-serial")
expect(cmd).to_contain("none")
expect(cmd.contains("stdio")).to_equal(false)
expect(cmd.contains("-display")).to_equal(false)
```

</details>

#### enables gui serial output only in the explicit debug lane

- enables gui serial output only in the explicit debug lane
   - Expected: cmd does not contain `-display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables gui serial output only in the explicit debug lane")
val target = get_gui_target()
val cmd = build_qemu_command_with_options(target, qemu_run_options_debug_gui())
expect(cmd).to_contain("-serial")
expect(cmd).to_contain("stdio")
expect(cmd.contains("-display")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/qemu_runner_desktop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `172800b38fca56eac3f3fc5786a33f8361b676cbb65779ba9fa2a38b17f183fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `172800b38fca56eac3f3fc5786a33f8361b676cbb65779ba9fa2a38b17f183fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `172800b38fca56eac3f3fc5786a33f8361b676cbb65779ba9fa2a38b17f183fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/unit/os/qemu_runner_desktop_spec.spl
mirror: doc/06_spec/unit/os/qemu_runner_desktop_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/qemu_runner_desktop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/qemu_runner_desktop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/qemu_runner_desktop_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/os/qemu_runner_desktop_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/qemu_runner_desktop_spec.spl:201:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a desktop UEFI validator command requiring structured FAT checks for migrated tool apps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/qemu_runner_desktop_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines a BGA WM Simple Web Engine2D scenario' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/qemu_runner_desktop_spec.spl:268:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires WM Simple Web render markers instead of a bare TEST PASSED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
