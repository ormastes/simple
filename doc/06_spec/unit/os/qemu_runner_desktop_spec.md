# Qemu Runner Desktop Specification

## Scenarios

#### builds a desktop UEFI validator command requiring structured FAT checks for migrated tool apps

<details>
<summary>Executable SPipe</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(target.entry).to_equal("examples/simple_os/arch/x86_64/gui_entry_engine2d.spl")
expect(target.output).to_equal("build/os/simpleos_wm_simple_web_check_32.elf")
expect(target.qemu_memory).to_equal("2G")

val direct_target = get_wm_simple_web_check_target()
expect(direct_target.entry).to_equal(target.entry)
val sources = os_native_build_sources(direct_target)
expect(sources).to_contain("build/os/generated")
expect(sources).to_contain("src/os")
expect(sources).to_contain("src/lib")
expect(sources).to_contain("examples/simple_os/arch/x86_64")
expect(sources.contains("examples/simple_os")).to_equal(false)

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

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(ssh_probe_target.entry).to_equal("examples/simple_os/arch/x86_64/ssh_x25519_probe_entry.spl")
expect(ssh_probe_target.output).to_equal("build/os/simpleos_ssh_x25519_probe_32.elf")
```

</details>

#### keeps gui targets quiet by default

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

