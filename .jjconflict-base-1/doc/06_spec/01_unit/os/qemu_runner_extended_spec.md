# Qemu Runner Extended Specification

> <details>

<!-- sdn-diagram:id=qemu_runner_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_runner_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_runner_extended_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_runner_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Extended Specification

## Scenarios

### Qemu runner native-build prerequisites

#### passes entry closure for the x86_64 OS entry build

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_os_build_backend_for_target(get_target(Architecture.Riscv32))).to_equal("llvm")
expect(default_os_build_backend_for_target(get_target(Architecture.Riscv64))).to_equal("llvm")
expect(default_os_build_backend_for_target(get_target(Architecture.Arm64))).to_equal("llvm")
expect(default_os_build_backend_for_target(get_target(Architecture.Arm32))).to_equal("llvm")
```

</details>

#### explains when the selected compiler lacks the LLVM backend

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "LLVM backend requested but 'llvm' feature not enabled"
val hint = native_build_prerequisite_hint("llvm", stderr)
expect(hint).to_contain("Rust `llvm` feature")
expect(hint).to_contain("LLVM 18")
```

</details>

#### explains when cranelift cannot initialize a freestanding target

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "Compilation error: Support for this target has not been implemented yet"
val hint = native_build_prerequisite_hint("cranelift", stderr)
expect(hint).to_contain("Cranelift cannot build this freestanding target")
expect(hint).to_contain("LLVM-enabled")
```

</details>

#### adds the generated SSH live marker source to the live build source set

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sources = os_native_build_sources(get_ssh_live_target())
expect(sources).to_contain("src/os")
expect(sources).to_contain("src/lib")
expect(sources).to_contain("examples/09_embedded/simple_os")
expect(sources).to_contain("build/os/generated")
```

</details>

#### uses the baremetal bootstrap env for the SSH live target

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_prefix = os_native_build_env_prefix(get_ssh_live_target(), "")
expect(env_prefix).to_contain("SIMPLE_BOOTSTRAP=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
```

</details>

#### uses the baremetal bootstrap env for the SSH X25519 probe target

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_prefix = os_native_build_env_prefix(get_ssh_x25519_probe_target(), "")
expect(env_prefix).to_contain("SIMPLE_BOOTSTRAP=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
```

</details>

#### uses the ARM64 WM QEMU build contract for ramfb source and env setup

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_arm64_wm_qemu_target()
val sources = os_native_build_sources(target)
expect(sources).to_contain("build/os/generated")
expect(sources).to_contain("src/os")
expect(sources).to_contain("examples/09_embedded/simple_os")
expect(sources.contains("src/lib")).to_equal(false)
val env_prefix = os_native_build_env_prefix(target, "")
expect(env_prefix).to_contain("SIMPLE_BOOTSTRAP=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix).to_contain("SIMPLE_ALLOW_FREESTANDING_STUBS=1")
```

</details>

#### resolves the named ARM64 WM ramfb scenario to the WM target

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_arm64_wm_ramfb()
val target = scenario_target(scenario)
val cmd = build_scenario_command(scenario, target.output)
expect(scenario_name_or_missing("arm64-wm-ramfb")).to_equal("arm64-wm-ramfb")
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/wm_entry.spl")
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_arm64_wm_ramfb()
val serial = arm64_wm_ramfb_required_marker_fragments().join("\n")
expect(qemu_scenario_serial_accepts_completion(scenario, "", serial)).to_equal(true)
expect(scenario_qemu_exit_success(scenario, 124)).to_equal(false)
```

</details>

#### keeps RV64 hosted builds on minimal boot sources without freestanding unresolved-symbol stubs

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hosted_target = scenario_target(scenario_riscv64_hosted())
val env_prefix = os_native_build_env_prefix(hosted_target, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps ARM64 smoke builds on minimal boot sources without freestanding unresolved-symbol stubs

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs_exec = scenario_target(scenario_arm64_virtio_fat32_smf())
val env_prefix = os_native_build_env_prefix(fs_exec, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps ARM32 fs-exec on minimal boot sources without freestanding unresolved-symbol stubs

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs_exec = scenario_target(scenario_arm32_virtio_fat32_smf())
val env_prefix = os_native_build_env_prefix(fs_exec, "")
expect(env_prefix).to_contain("SIMPLE_BOOT_MINIMAL=1")
expect(env_prefix).to_contain("SIMPLE_LIB=\"$(pwd)/src\"")
expect(env_prefix.contains("SIMPLE_ALLOW_FREESTANDING_STUBS=1")).to_equal(false)
```

</details>

#### keeps the checked-in generated fallback aligned with the enabled override template

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fallback = rt_file_read_text("src/generated/simpleos_log_config.spl")
expect(fallback).to_equal(_simpleos_log_config_source(true))
```

</details>

#### does not reuse a stale SSH live artifact after a failed build

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = desktop_disk_image_candidates()
expect(candidates[0]).to_start_with("release/")
expect(candidates[1]).to_equal("build/os/fat32-x86_64.img")
expect(candidates[2]).to_equal("build/os/fat32.img")
```

</details>

#### materializes the desktop disk lane at the platform image path

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = desktop_disk_make_script_args("build/os/fat32-x86_64.img")
expect(args[0]).to_equal("scripts/os/make_os_disk.shs")
expect(args[1]).to_equal("64")
expect(args[2]).to_equal("build/os/fat32-x86_64.img")
```

</details>

#### resolves the release disk path when the release artifact exists

1. rt dir create all
   - Expected: rt_file_write_text(release_path, "disk-image") is true
   - Expected: desktop_disk_image_path_in(release_root) equals `release_path`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val release_root = "build/test-qemu-release-artifacts"
val release_path = desktop_release_disk_image_path_in(release_root)
rt_dir_create_all("{release_root}/x86_64/images")
expect(rt_file_write_text(release_path, "disk-image")).to_equal(true)
expect(desktop_disk_image_path_in(release_root)).to_equal(release_path)
```

</details>

#### exposes the future installer ISO path hook

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iso_path = desktop_release_installer_iso_path()
expect(iso_path).to_end_with(".iso")
val candidates = desktop_installer_iso_candidates()
expect(candidates[0]).to_equal(iso_path)
```

</details>

### Qemu runner board bundle smoke

#### materializes representative board bundle outputs through deterministic host-side shims

1. x64 ok = ensure board bundle

2. arm64 ok = ensure board bundle

3. riscv64 ok = ensure board bundle
   - Expected: setup_ok is true
   - Expected: restore_ok is true
   - Expected: x64_ok is true
   - Expected: arm64_ok is true
   - Expected: riscv64_ok is true
   - Expected: rt_file_exists(x64_output) is true
   - Expected: rt_file_exists(arm64_output) is true
   - Expected: rt_file_exists(riscv64_output + "/board_linux_boot_products.sdn") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(x64_cmd[2]).to_contain("scripts/os/make_os_disk.shs")
expect(x64_cmd[2]).to_contain("x86_64")
expect(x64_cmd[3]).to_equal("simpleos-uefi-disk")
expect(x64_cmd[4]).to_equal(kernel_path)
expect(x64_cmd[5]).to_equal(x64_output)

val arm64_cmd = board_bundle_command("arm64", kernel_path, arm64_output)
expect(arm64_cmd).to_equal(["/bin/sh", "scripts/os/make_os_disk.shs", "64", arm64_output, "", "arm64"])

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

1. riscv64 ok = test board lane
   - Expected: setup_ok is true
   - Expected: restore_ok is true
   - Expected: riscv64_ok is true
   - Expected: rt_file_exists(riscv64_output + "/board_linux_boot_products.sdn") is true
   - Expected: rt_file_exists(riscv64_output + "/products/run.log") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu_runner_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Qemu runner native-build prerequisites
- Qemu runner release artifacts
- Qemu runner board bundle smoke
- Qemu runner board execution smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
