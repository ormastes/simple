# @manual: primary

> Purpose: Prove that Qemu runner native-build prerequisites.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Qemu runner native-build prerequisites.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/qemu_runner_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Qemu runner native-build prerequisites.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-001
doc/01_research/local/REQ-OS-001.md
doc/03_plan/sys_test/REQ-OS-001.md
doc/04_architecture/REQ-OS-001.md
doc/05_design/REQ-OS-001.md

## Scenarios

### Qemu runner native-build prerequisites

#### passes entry closure for the x86_64 OS entry build

- Verify: passes entry closure for the x86_64 OS entry build
   - Expected: args does not contain `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: passes entry closure for the x86_64 OS entry build")
val target = OsTarget(
    arch: Architecture.X86_64,
    entry: "examples/09_embedded/simple_os/arch/x86_64/os_entry.spl",
    linker_script: "examples/09_embedded/simple_os/arch/x86_64/linker.ld",
    target_triple: "x86_64-unknown-none",
    output: "build/os/simpleos_x86_64.elf",
    qemu_system: "qemu-system-x86_64",
    qemu_machine: "q35",
    qemu_cpu: "qemu64",
    qemu_memory: "128M",
    qemu_bios: "",
    qemu_extra: [],
    gui_mode: false
)
val args = os_native_build_args(target, "llvm")
expect(args).to_contain("--entry-closure")
expect(args).to_contain("--entry")
expect(args).to_contain("examples/09_embedded/simple_os/arch/x86_64/os_entry.spl")
expect(args.contains("examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl")).to_equal(false)
```

</details>

#### defaults RISC-V OS targets to LLVM native-build backend

- Verify: defaults RISC-V OS targets to LLVM native-build backend
   - Expected: default_os_build_backend_for_target(get_target(Architecture.Riscv32)) equals `llvm`
   - Expected: default_os_build_backend_for_target(get_target(Architecture.Riscv64)) equals `llvm`
   - Expected: default_os_build_backend_for_target(get_target(Architecture.Arm64)) equals `llvm`
   - Expected: default_os_build_backend_for_target(get_target(Architecture.Arm32)) equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: defaults RISC-V OS targets to LLVM native-build backend")
expect(default_os_build_backend_for_target(get_target(Architecture.Riscv32))).to_equal("llvm")
expect(default_os_build_backend_for_target(get_target(Architecture.Riscv64))).to_equal("llvm")
expect(default_os_build_backend_for_target(get_target(Architecture.Arm64))).to_equal("llvm")
expect(default_os_build_backend_for_target(get_target(Architecture.Arm32))).to_equal("llvm")
```

</details>

#### explains when the selected compiler lacks the LLVM backend

- Verify: explains when the selected compiler lacks the LLVM backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: explains when the selected compiler lacks the LLVM backend")
val stderr = "LLVM backend requested but 'llvm' feature not enabled"
val hint = native_build_prerequisite_hint("llvm", stderr)
expect(hint).to_contain("Rust `llvm` feature")
expect(hint).to_contain("LLVM 18")
```

</details>

#### explains when cranelift cannot initialize a freestanding target

- Verify: explains when cranelift cannot initialize a freestanding target


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: explains when cranelift cannot initialize a freestanding target")
val stderr = "Compilation error: Support for this target has not been implemented yet"
val hint = native_build_prerequisite_hint("cranelift", stderr)
expect(hint).to_contain("Cranelift cannot build this freestanding target")
expect(hint).to_contain("LLVM-enabled")
```

</details>

#### adds the generated SSH live marker source to the live build source set

- Verify: adds the generated SSH live marker source to the live build source set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: adds the generated SSH live marker source to the live build source set")
val sources = os_native_build_sources(get_ssh_live_target())
expect(sources).to_contain("src/os")
expect(sources).to_contain("src/lib")
expect(sources).to_contain("examples/simple_os")
expect(sources).to_contain("build/os/generated")
```

</details>

#### uses the baremetal bootstrap env for the SSH live target

- Verify: uses the baremetal bootstrap env for the SSH live target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: uses the baremetal bootstrap env for the SSH live target")
val env_prefix = os_native_build_env_prefix(get_ssh_live_target(), "")
expect(env_prefix).to_contain("SIMPLE_BOOTSTRAP=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
```

</details>

#### uses the baremetal bootstrap env for the SSH X25519 probe target

- Verify: uses the baremetal bootstrap env for the SSH X25519 probe target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: uses the baremetal bootstrap env for the SSH X25519 probe target")
val env_prefix = os_native_build_env_prefix(get_ssh_x25519_probe_target(), "")
expect(env_prefix).to_contain("SIMPLE_BOOTSTRAP=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
```

</details>

#### uses the ARM64 WM QEMU build contract for ramfb source and env setup

- Verify: uses the ARM64 WM QEMU build contract for ramfb source and env setup


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: uses the ARM64 WM QEMU build contract for ramfb source and env setup")
val target = get_arm64_wm_qemu_target()
val sources = os_native_build_sources(target)
expect(sources).to_contain("build/os/generated")
expect(sources).to_contain("src/os")
expect(sources).to_contain("src/lib")
expect(sources).to_contain("examples/simple_os")
val env_prefix = os_native_build_env_prefix(target, "")
expect(env_prefix).to_contain("SIMPLE_BOOTSTRAP=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix).to_contain("SIMPLE_ALLOW_FREESTANDING_STUBS=1")
```

</details>

#### selects portable ARM64 WM acceleration by host

- Verify: selects portable ARM64 WM acceleration by host
   - Expected: arm64_wm_qemu_cpu_for_host("macos", "aarch64") equals `host`
   - Expected: arm64_wm_qemu_extra_for_host("macos", "aarch64") equals `["-accel", "hvf", "-device", "ramfb"]`
   - Expected: arm64_wm_qemu_cpu_for_host("linux", "x86_64") equals `cortex-a57`
   - Expected: arm64_wm_qemu_extra_for_host("linux", "x86_64") equals `["-accel", "tcg", "-device", "ramfb"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: selects portable ARM64 WM acceleration by host")
expect(arm64_wm_qemu_cpu_for_host("macos", "aarch64")).to_equal("host")
expect(arm64_wm_qemu_extra_for_host("macos", "aarch64")).to_equal(["-accel", "hvf", "-device", "ramfb"])
expect(arm64_wm_qemu_cpu_for_host("linux", "x86_64")).to_equal("cortex-a57")
expect(arm64_wm_qemu_extra_for_host("linux", "x86_64")).to_equal(["-accel", "tcg", "-device", "ramfb"])
```

</details>

#### resolves the named ARM64 WM ramfb scenario to the WM target

- Verify: resolves the named ARM64 WM ramfb scenario to the WM target
   - Expected: scenario_name_or_missing("arm64-wm-ramfb") equals `arm64-wm-ramfb`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl`
   - Expected: target.output equals `build/os/simpleos_arm64_wm.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: resolves the named ARM64 WM ramfb scenario to the WM target")
val scenario = scenario_arm64_wm_ramfb()
val target = scenario_target(scenario)
val cmd = build_scenario_command(scenario, target.output)
expect(scenario_name_or_missing("arm64-wm-ramfb")).to_equal("arm64-wm-ramfb")
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl")
expect(target.output).to_equal("build/os/simpleos_arm64_wm.elf")
expect(cmd).to_contain("qemu-system-aarch64")
expect(cmd).to_contain("-serial")
expect(cmd).to_contain("file:" + arm64_wm_ramfb_serial_log_path())
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_arm64_wm.elf")
expect(cmd).to_contain("-device")
expect(cmd).to_contain("ramfb")
```

</details>

#### accepts ARM64 WM ramfb marker completion even when QEMU remains live

- Verify: accepts ARM64 WM ramfb marker completion even when QEMU remains live
   - Expected: qemu_scenario_serial_accepts_completion(scenario, "", serial) is true
   - Expected: scenario_qemu_exit_success(scenario, 124) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: accepts ARM64 WM ramfb marker completion even when QEMU remains live")
val scenario = scenario_arm64_wm_ramfb()
val serial = arm64_wm_ramfb_required_marker_fragments().join("\n")
expect(qemu_scenario_serial_accepts_completion(scenario, "", serial)).to_equal(true)
expect(scenario_qemu_exit_success(scenario, 124)).to_equal(false)
```

</details>

#### keeps RV64 hosted builds on minimal boot sources without freestanding unresolved-symbol stubs

- Verify: keeps RV64 hosted builds on minimal boot sources without freestanding unresolved-symbol stubs
   - Expected: env_prefix does not contain `SIMPLE_ALLOW_FREESTANDING_STUBS=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: keeps RV64 hosted builds on minimal boot sources without freestanding unresolved-symbol stubs")
val hosted_target = scenario_target(scenario_riscv64_hosted())
val env_prefix = os_native_build_env_prefix(hosted_target, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps ARM64 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs

- Verify: keeps ARM64 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs
   - Expected: env_prefix does not contain `SIMPLE_ALLOW_FREESTANDING_STUBS=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: keeps ARM64 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs")
val smoke = OsTarget(
    arch: Architecture.Arm64,
    entry: "examples/09_embedded/simple_os/arch/arm64/smoke_entry.spl",
    linker_script: "examples/09_embedded/simple_os/arch/arm64/fs_exec_linker.ld",
    target_triple: "aarch64-unknown-none",
    output: "build/os/simpleos_arm64_smoke.elf",
    qemu_system: "qemu-system-aarch64",
    qemu_machine: "virt",
    qemu_cpu: "cortex-a72",
    qemu_memory: "128M",
    qemu_bios: "",
    qemu_extra: [],
    gui_mode: false
)
val env_prefix = os_native_build_env_prefix(smoke, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps ARM32 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs

- Verify: keeps ARM32 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs
   - Expected: env_prefix does not contain `SIMPLE_ALLOW_FREESTANDING_STUBS=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: keeps ARM32 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs")
val smoke = OsTarget(
    arch: Architecture.Arm32,
    entry: "examples/09_embedded/simple_os/arch/arm32/smoke_entry.spl",
    linker_script: "examples/09_embedded/simple_os/arch/arm32/fs_exec_linker.ld",
    target_triple: "armv7-none-eabi",
    output: "build/os/simpleos_arm32_smoke.elf",
    qemu_system: "qemu-system-arm",
    qemu_machine: "virt",
    qemu_cpu: "cortex-a15",
    qemu_memory: "128M",
    qemu_bios: "",
    qemu_extra: [],
    gui_mode: false
)
val env_prefix = os_native_build_env_prefix(smoke, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps ARM64 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs

- Verify: keeps ARM64 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs
   - Expected: env_prefix does not contain `SIMPLE_ALLOW_FREESTANDING_STUBS=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: keeps ARM64 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs")
val fs_exec = scenario_target(scenario_arm64_virtio_fat32_smf())
val env_prefix = os_native_build_env_prefix(fs_exec, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps ARM32 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs

- Verify: keeps ARM32 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs
   - Expected: env_prefix does not contain `SIMPLE_ALLOW_FREESTANDING_STUBS=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: keeps ARM32 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs")
val fs_exec = scenario_target(scenario_arm32_virtio_fat32_smf())
val env_prefix = os_native_build_env_prefix(fs_exec, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps the checked-in generated fallback aligned with the enabled override template

- Verify: keeps the checked-in generated fallback aligned with the enabled override template
   - Expected: fallback equals `_simpleos_log_config_source(true)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: keeps the checked-in generated fallback aligned with the enabled override template")
val fallback = rt_file_read_text("src/generated/simpleos_log_config.spl")
expect(fallback).to_equal(_simpleos_log_config_source(true))
```

</details>

#### does not reuse a stale SSH live artifact after a failed build

- Verify: does not reuse a stale SSH live artifact after a failed build
   - Expected: rt_dir_create_all("build/os") is true
   - Expected: rt_file_write_text(target.output, "stale-kernel") is true
   - Expected: rt_file_exists(target.output) is true
   - Expected: rt_env_set("SIMPLE_BINARY", install_failing_simple_shim("build/test-qemu-failing-simple/stale", 42)) is true
   - Expected: built is false
   - Expected: rt_file_exists(target.output) is false
   - Expected: rt_env_set("SIMPLE_BINARY", "bin/simple") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: does not reuse a stale SSH live artifact after a failed build")
val target = get_ssh_live_target()
expect(rt_dir_create_all("build/os")).to_equal(true)
expect(rt_file_write_text(target.output, "stale-kernel")).to_equal(true)
expect(rt_file_exists(target.output)).to_equal(true)
expect(rt_env_set("SIMPLE_BINARY", install_failing_simple_shim("build/test-qemu-failing-simple/stale", 42))).to_equal(true)

val built = build_os_with_backend(target, "cranelift")

expect(built).to_equal(false)
expect(rt_file_exists(target.output)).to_equal(false)
expect(rt_env_set("SIMPLE_BINARY", "bin/simple")).to_equal(true)
```

</details>

#### cleans up the generated log config override after a failed build

- Verify: cleans up the generated log config override after a failed build
   - Expected: rt_env_set("PATH", "/tmp/simple-path-before-build") is true
   - Expected: rt_env_set("SIMPLE_BINARY", install_failing_simple_shim("build/test-qemu-failing-simple/log-config", 43)) is true
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "off") is true
   - Expected: rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", "prior-marker") is true
   - Expected: built is false
   - Expected: rt_file_exists(config_path) is false
   - Expected: rt_env_get("PATH") ?? "" equals `/tmp/simple-path-before-build`
   - Expected: rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? "" equals `prior-marker`
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "on") is true
   - Expected: rt_env_set("SIMPLE_BINARY", "bin/simple") is true
   - Expected: rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", original_marker) is true
   - Expected: rt_env_set("PATH", original_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: cleans up the generated log config override after a failed build")
val target = get_ssh_live_target()
val config_path = "build/os/generated/generated/simpleos_log_config.spl"
val original_path = rt_env_get("PATH") ?? ""
val original_marker = rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? ""
expect(rt_env_set("PATH", "/tmp/simple-path-before-build")).to_equal(true)
expect(rt_env_set("SIMPLE_BINARY", install_failing_simple_shim("build/test-qemu-failing-simple/log-config", 43))).to_equal(true)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "off")).to_equal(true)
expect(rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", "prior-marker")).to_equal(true)

val built = build_os_with_backend(target, "cranelift")

expect(built).to_equal(false)
expect(rt_file_exists(config_path)).to_equal(false)
expect(rt_env_get("PATH") ?? "").to_equal("/tmp/simple-path-before-build")
expect(rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? "").to_equal("prior-marker")
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "on")).to_equal(true)
expect(rt_env_set("SIMPLE_BINARY", "bin/simple")).to_equal(true)
expect(rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", original_marker)).to_equal(true)
expect(rt_env_set("PATH", original_path)).to_equal(true)
```

</details>

#### cleans up the generated log config override after a prepare-stage failure

- Verify: cleans up the generated log config override after a prepare-stage failure
   - Expected: rt_env_set("SIMPLE_BINARY", "bin/simple") is true
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "off") is true
   - Expected: rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", "prepare-prior-marker") is true
   - Expected: shell_exit_code("rm -rf \"" + marker_path + "\"") equals `0`
   - Expected: rt_dir_create_all(marker_path) is true
   - Expected: built is false
   - Expected: rt_file_exists(config_path) is false
   - Expected: shell_exit_code("rm -rf \"" + marker_path + "\"") equals `0`
   - Expected: rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? "" equals `prepare-prior-marker`
   - Expected: rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", original_marker) is true
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "on") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: cleans up the generated log config override after a prepare-stage failure")
val target = get_ssh_live_target()
val config_path = "build/os/generated/generated/simpleos_log_config.spl"
val marker_path = "build/os/generated/ssh_live_build_marker.spl"
val original_marker = rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? ""
expect(rt_env_set("SIMPLE_BINARY", "bin/simple")).to_equal(true)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "off")).to_equal(true)
expect(rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", "prepare-prior-marker")).to_equal(true)
expect(shell_exit_code("rm -rf \"" + marker_path + "\"")).to_equal(0)
expect(rt_dir_create_all(marker_path)).to_equal(true)

val built = build_os_with_backend(target, "cranelift")

expect(built).to_equal(false)
expect(rt_file_exists(config_path)).to_equal(false)
expect(shell_exit_code("rm -rf \"" + marker_path + "\"")).to_equal(0)
expect(rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? "").to_equal("prepare-prior-marker")
expect(rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", original_marker)).to_equal(true)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "on")).to_equal(true)
```

</details>

#### restores the prior SSH live marker and PATH on native-build failure

- Verify: restores the prior SSH live marker and PATH on native-build failure
   - Expected: rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", "tooling-prior-marker") is true
   - Expected: rt_env_set("SIMPLE_BINARY", install_failing_simple_shim("build/test-qemu-failing-simple/tooling", 44)) is true
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "off") is true
   - Expected: rt_env_set("PATH", "/tmp/simple-path-tooling-failure") is true
   - Expected: built is false
   - Expected: rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? "" equals `tooling-prior-marker`
   - Expected: rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", original_marker) is true
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "on") is true
   - Expected: rt_env_set("SIMPLE_BINARY", original_simple_binary) is true
   - Expected: rt_env_set("PATH", original_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: restores the prior SSH live marker and PATH on native-build failure")
val target = get_ssh_live_target()
val original_marker = rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? ""
val original_path = rt_env_get("PATH") ?? ""
val original_simple_binary = rt_env_get("SIMPLE_BINARY") ?? ""
expect(rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", "tooling-prior-marker")).to_equal(true)
expect(rt_env_set("SIMPLE_BINARY", install_failing_simple_shim("build/test-qemu-failing-simple/tooling", 44))).to_equal(true)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "off")).to_equal(true)
expect(rt_env_set("PATH", "/tmp/simple-path-tooling-failure")).to_equal(true)

val built = build_os_with_backend(target, "cranelift")

expect(built).to_equal(false)
expect(rt_env_get("SIMPLE_SSH_LIVE_BUILD_MARKER") ?? "").to_equal("tooling-prior-marker")
expect(rt_env_set("SIMPLE_SSH_LIVE_BUILD_MARKER", original_marker)).to_equal(true)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "on")).to_equal(true)
expect(rt_env_set("SIMPLE_BINARY", original_simple_binary)).to_equal(true)
expect(rt_env_set("PATH", original_path)).to_equal(true)
```

</details>

### Qemu runner release artifacts

#### prefers release disk images before platform and legacy build fixtures

- Verify: prefers release disk images before platform and legacy build fixtures
   - Expected: candidates[1] equals `build/os/fat32-x86_64.img`
   - Expected: candidates[2] equals `build/os/fat32.img`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: prefers release disk images before platform and legacy build fixtures")
val candidates = desktop_disk_image_candidates()
expect(candidates[0]).to_start_with("release/")
expect(candidates[1]).to_equal("build/os/fat32-x86_64.img")
expect(candidates[2]).to_equal("build/os/fat32.img")
```

</details>

#### materializes the desktop disk lane at the platform image path

- Verify: materializes the desktop disk lane at the platform image path
   - Expected: args[0] equals `scripts/make_os_disk.shs`
   - Expected: args[1] equals `64`
   - Expected: args[2] equals `build/os/fat32-x86_64.img`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: materializes the desktop disk lane at the platform image path")
val args = desktop_disk_make_script_args("build/os/fat32-x86_64.img")
expect(args[0]).to_equal("scripts/make_os_disk.shs")
expect(args[1]).to_equal("64")
expect(args[2]).to_equal("build/os/fat32-x86_64.img")
```

</details>

#### resolves the release disk path when the release artifact exists

- Verify: resolves the release disk path when the release artifact exists
   - Expected: rt_file_write_text(release_path, "disk-image") is true
   - Expected: desktop_disk_image_path_in(release_root) equals `release_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: resolves the release disk path when the release artifact exists")
val release_root = "build/test-qemu-release-artifacts"
val release_path = desktop_release_disk_image_path_in(release_root)
rt_dir_create_all("{release_root}/x86_64/images")
expect(rt_file_write_text(release_path, "disk-image")).to_equal(true)
expect(desktop_disk_image_path_in(release_root)).to_equal(release_path)
```

</details>

#### exposes the future installer ISO path hook

- Verify: exposes the future installer ISO path hook
   - Expected: candidates[0] equals `iso_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: exposes the future installer ISO path hook")
val iso_path = desktop_release_installer_iso_path()
expect(iso_path).to_end_with(".iso")
val candidates = desktop_installer_iso_candidates()
expect(candidates[0]).to_equal(iso_path)
```

</details>

### Qemu runner board bundle smoke

#### materializes representative board bundle outputs through deterministic host-side shims

- Verify: materializes representative board bundle outputs through deterministic host-side shims
   - Expected: rt_dir_create_all(root) is true
   - Expected: rt_file_write_text(kernel_path, "kernel") is true
   - Expected: x64_cmd[0] equals `/bin/sh`
   - Expected: x64_cmd[1] equals `-c`
   - Expected: x64_cmd[3] equals `simpleos-uefi-disk`
   - Expected: x64_cmd[4] equals `kernel_path`
   - Expected: x64_cmd[5] equals `x64_output`
   - Expected: arm64_cmd equals `["/bin/sh", "scripts/make_os_disk.shs", "64", arm64_output, "", "arm64"]`
   - Expected: riscv64_cmd equals `[`
   - Expected: setup_ok is true
   - Expected: restore_ok is true
   - Expected: x64_ok is true
   - Expected: arm64_ok is true
   - Expected: riscv64_ok is true
   - Expected: rt_file_exists(x64_output) is true
   - Expected: rt_file_exists(arm64_output) is true
   - Expected: rt_file_exists(riscv64_output + "/board_linux_boot_products.sdn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: materializes representative board bundle outputs through deterministic host-side shims")
val root = "build/test-qemu-board-bundle-smoke"
val kernel_path = root + "/kernel.elf"
val x64_output = root + "/x64-board.img"
val arm64_output = root + "/arm64-board.img"
val riscv64_output = root + "/riscv64-board"
expect(rt_dir_create_all(root)).to_equal(true)
expect(rt_file_write_text(kernel_path, "kernel")).to_equal(true)

val x64_cmd = board_bundle_command("x86_64", kernel_path, x64_output)
expect(x64_cmd[0]).to_equal("/bin/sh")
expect(x64_cmd[1]).to_equal("-c")
expect(x64_cmd[2]).to_contain("scripts/make_os_disk.shs")
expect(x64_cmd[2]).to_contain("x86_64")
expect(x64_cmd[3]).to_equal("simpleos-uefi-disk")
expect(x64_cmd[4]).to_equal(kernel_path)
expect(x64_cmd[5]).to_equal(x64_output)

val arm64_cmd = board_bundle_command("arm64", kernel_path, arm64_output)
expect(arm64_cmd).to_equal(["/bin/sh", "scripts/make_os_disk.shs", "64", arm64_output, "", "arm64"])

val riscv64_cmd = board_bundle_command("riscv64", kernel_path, riscv64_output)
expect(riscv64_cmd).to_equal([
    "bin/simple", "run", "src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl",
    "--", "--board=mlk_s02_100t", riscv64_output
])

val setup_ok = install_board_bundle_tooling_shims(root)
var x64_ok = false
var arm64_ok = false
var riscv64_ok = false
if setup_ok:
    x64_ok = ensure_board_bundle("x86_64", kernel_path, x64_output)
    arm64_ok = ensure_board_bundle("arm64", kernel_path, arm64_output)
    riscv64_ok = ensure_board_bundle("riscv64", kernel_path, riscv64_output)
val restore_ok = restore_board_bundle_tooling(root)

expect(setup_ok).to_equal(true)
expect(restore_ok).to_equal(true)
expect(x64_ok).to_equal(true)
expect(arm64_ok).to_equal(true)
expect(riscv64_ok).to_equal(true)
expect(rt_file_exists(x64_output)).to_equal(true)
expect(rt_file_exists(arm64_output)).to_equal(true)
expect(rt_file_exists(riscv64_output + "/board_linux_boot_products.sdn")).to_equal(true)
```

</details>

### Qemu runner board execution smoke

#### runs the representative riscv64 board lane through the generated-linux wrapper

- Verify: runs the representative riscv64 board lane through the generated-linux wrapper
   - Expected: rt_dir_create_all(root) is true
   - Expected: rt_file_write_text(kernel_path, "kernel") is true
   - Expected: cmd equals `[`
   - Expected: board_lane_test_command("x86_64", root).len() equals `4`
   - Expected: board_lane_test_command("arm64", root).len() equals `4`
   - Expected: setup_ok is true
   - Expected: restore_ok is true
   - Expected: riscv64_ok is true
   - Expected: rt_file_exists(riscv64_output + "/board_linux_boot_products.sdn") is true
   - Expected: rt_file_exists(riscv64_output + "/products/run.log") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: runs the representative riscv64 board lane through the generated-linux wrapper")
val root = "build/test-qemu-board-lane-smoke"
val kernel_path = root + "/kernel.elf"
val riscv64_output = root + "/riscv64-board"
expect(rt_dir_create_all(root)).to_equal(true)
expect(rt_file_write_text(kernel_path, "kernel")).to_equal(true)

val cmd = board_lane_test_command("riscv64", riscv64_output)
expect(cmd).to_equal([
    "/bin/sh",
    "scripts/mlk_s02_100t_generated_linux.shs",
    "--arch=rv64",
    "--bundle-root=" + riscv64_output,
    "--product-root=" + riscv64_output + "/products"
])
expect(board_lane_test_command("x86_64", root).len()).to_equal(4)
expect(board_lane_test_command("arm64", root).len()).to_equal(4)

val setup_ok = install_board_bundle_tooling_shims(root)
var riscv64_ok = false
if setup_ok:
    riscv64_ok = test_board_lane("riscv64", kernel_path, riscv64_output)
val restore_ok = restore_board_bundle_tooling(root)

expect(setup_ok).to_equal(true)
expect(restore_ok).to_equal(true)
expect(riscv64_ok).to_equal(true)
expect(rt_file_exists(riscv64_output + "/board_linux_boot_products.sdn")).to_equal(true)
expect(rt_file_exists(riscv64_output + "/products/run.log")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `669d9e6a63bec98fded02ea5a4684844f55a03b7cc6832277c23cf3f7ee19740`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `669d9e6a63bec98fded02ea5a4684844f55a03b7cc6832277c23cf3f7ee19740`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `669d9e6a63bec98fded02ea5a4684844f55a03b7cc6832277c23cf3f7ee19740`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/qemu_runner_extended_spec.spl
mirror: doc/06_spec/unit/os/qemu_runner_extended_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/os/qemu_runner_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/qemu_runner_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/qemu_runner_extended_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/qemu_runner_extended_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/qemu_runner_extended_spec.spl:221:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes entry closure for the x86_64 OS entry build' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/qemu_runner_extended_spec.spl:244:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults RISC-V OS targets to LLVM native-build backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/qemu_runner_extended_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'explains when the selected compiler lacks the LLVM backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
