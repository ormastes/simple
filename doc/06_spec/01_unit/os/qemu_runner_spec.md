# Qemu Runner Specification

> <details>

<!-- sdn-diagram:id=qemu_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_runner_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Specification

## Scenarios

### Qemu runner serial routing

#### does not accept non-x86 QEMU exit code 1 as success

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = get_target(Architecture.Arm64)
val arm32 = get_target(Architecture.Arm32)
val rv64 = get_target(Architecture.Riscv64)
expect(is_qemu_success(arm64, 1)).to_equal(false)
expect(is_qemu_success(arm32, 1)).to_equal(false)
expect(is_qemu_success(rv64, 1)).to_equal(false)
expect(is_qemu_success(arm64, 0)).to_equal(true)
```

</details>

#### keeps isa-debug-exit success limited to x86 scenarios

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = scenario_x64_desktop_uefi()
val arm64 = scenario_arm64_virtio_fat32_smf()
val rv64 = scenario_riscv64_virtio_fat32_smf()
expect(scenario_qemu_exit_success(x64, 1)).to_equal(true)
expect(scenario_qemu_exit_success(x64, 0)).to_equal(false)
expect(scenario_qemu_exit_success(arm64, 1)).to_equal(false)
expect(scenario_qemu_exit_success(rv64, 1)).to_equal(false)
expect(scenario_qemu_exit_success(arm64, 0)).to_equal(true)
```

</details>

#### exposes a runner-facing protection serial acceptance gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val an505_serial = "[BOOT] Platform: MPS2-AN505 (QEMU)\n[MPU] Enabled, 8 regions available, 4 configured\nSimpleOS Lite v0.5"
expect(qemu_protection_serial_accepts_hardening("mps2-an505", "enforce", "qemu", an505_serial)).to_equal(true)
expect(qemu_protection_serial_reason("mps2-an505", "enforce", "none", an505_serial)).to_equal("missing-runtime-check")

val detect_serial = "protection_probe=pass\n"
expect(qemu_protection_serial_accepts_hardening("mps2-an505", "detect", "qemu", detect_serial)).to_equal(false)
expect(qemu_protection_serial_reason("mps2-an505", "detect", "qemu", detect_serial)).to_equal("diagnostic-protection-mode:detect")

val fault_missing = "protection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\n"
expect(qemu_protection_serial_reason("stm32u585-uno-q", "fault-test", "real-board", fault_missing)).to_equal("missing-fault-recovery")
```

</details>

#### maps known QEMU scenarios to board protection gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = scenario_x64_net_user()
val x64_serial = "[BOOT64] call _start\n[harden] text_write_trap=pass\nTEST PASSED"
expect(qemu_scenario_protection_board_id(x64)).to_equal("x86_64-q35")
expect(qemu_scenario_protection_serial_accepts_hardening(x64, "enforce", x64_serial)).to_equal(true)

val rv64 = scenario_riscv64_hosted()
val rv64_serial = "[PAGING] MMU enabled (SCTLR_EL1.M=1, C=1, I=1)\npage_contract=pass\nTEST PASSED"
expect(qemu_scenario_protection_board_id(rv64)).to_equal("riscv64-virt")
expect(qemu_scenario_protection_serial_accepts_hardening(rv64, "enforce", rv64_serial)).to_equal(true)

val arm64 = scenario_arm64_virtio_fat32_smf()
expect(qemu_scenario_protection_board_id(arm64)).to_equal("")
expect(qemu_scenario_protection_serial_reason(arm64, "enforce", "protection_probe=pass")).to_equal("unsupported-qemu-board:arm64-virtio-fat32-smf")
```

</details>

#### enumerates 32-bit x86 as a first-class target

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var found_x86_32 = false
for target in get_all_targets():
    if target.arch == Architecture.X86:
        found_x86_32 = true
        expect(target.target_triple).to_equal("i686-unknown-none")
        expect(target.qemu_system).to_equal("qemu-system-i386")
expect(found_x86_32).to_equal(true)
```

</details>

#### launches the x86_32 kernel lane through the compatible QEMU frontend

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.X86)
val cmd = build_qemu_command(target)
expect(target.qemu_system).to_equal("qemu-system-i386")
expect(cmd[0]).to_equal("qemu-system-x86_64")
expect(cmd).to_contain("-machine")
expect(cmd).to_contain("pc")
expect(cmd).to_contain("-cpu")
expect(cmd).to_contain("qemu32")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_x86_32.elf")
```

</details>

#### builds normal targets from the shared platform catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86_64 = get_target(Architecture.X86_64)
expect(x86_64.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/boot_stage1_entry.spl")
expect(x86_64.linker_script).to_equal("examples/09_embedded/simple_os/arch/x86_64/linker.ld")
expect(x86_64.target_triple).to_equal("x86_64-unknown-none")
expect(x86_64.qemu_system).to_equal("qemu-system-x86_64")

val arm32 = get_target(Architecture.Arm32)
expect(arm32.entry).to_equal("src/os/kernel/arch/arm32/boot.spl")
expect(arm32.target_triple).to_equal("armv7-unknown-none-eabihf")
expect(arm32.qemu_system).to_equal("qemu-system-arm")
```

</details>

#### routes default ARM QEMU targets to the fs-exec acceptance lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = get_qemu_target(Architecture.Arm64)
expect(arm64.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl")
expect(arm64.output).to_equal("build/os/simpleos_arm64_fs_exec.elf")
val arm32 = get_qemu_target(Architecture.Arm32)
expect(arm32.entry).to_equal("examples/09_embedded/simple_os/arch/arm32/fs_exec_entry.spl")
expect(arm32.output).to_equal("build/os/simpleos_arm32_fs_exec.elf")
```

</details>

#### requires four-app fs launch markers for ARM acceptance lanes

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val markers = arm_fs_exec_required_marker_fragments(scenario_arm64_virtio_fat32_smf())
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=simple_compiler pid=")
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=simple_loader pid=")
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=clang pid=")
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=rust pid=")
expect(markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/simple_compiler bytes=")
expect(markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/simple_loader bytes=")
expect(markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/clang bytes=")
expect(markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/rust bytes=")
expect(markers.contains("[desktop-e2e] process-backed:ok app=hello_world pid=")).to_equal(false)
expect(markers.contains("[desktop-e2e] process-backed:ok app=simple_interpreter pid=")).to_equal(false)
expect(markers.contains("[desktop-e2e] process-backed:ok app=llvm pid=")).to_equal(false)
val lane = simpleos_platform_qemu_lane("arm64", "arm64-virtio-fat32-smf")
if val resolved_lane = lane:
    expect(markers).to_equal(resolved_lane.required_serial_markers)
else:
    fail("missing arm64 acceptance lane")
```

</details>

#### keeps ARM and RV64 marker helper surfaces aligned with catalog lanes

1. fail
   - Expected: arm_fs_exec_required_marker_fragments(scenario_arm32_virtio_fat32_smf()) equals `lane.required_serial_markers`
2. fail
   - Expected: riscv64_hosted_required_marker_fragments() equals `lane.required_serial_markers`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64_lane = simpleos_platform_qemu_lane("arm64", "arm64-virtio-fat32-smf")
if val lane = arm64_lane:
    expect(arm_fs_exec_required_marker_fragments(scenario_arm64_virtio_fat32_smf())).to_equal(lane.required_serial_markers)
else:
    fail("missing arm64 virtio lane")

val arm32_lane = simpleos_platform_qemu_lane("arm32", "arm32-virtio-fat32-smf")
if val lane = arm32_lane:
    expect(arm_fs_exec_required_marker_fragments(scenario_arm32_virtio_fat32_smf())).to_equal(lane.required_serial_markers)
else:
    fail("missing arm32 virtio lane")

val rv64_hosted_lane = simpleos_platform_qemu_lane("riscv64", "riscv64-hosted")
if val lane = rv64_hosted_lane:
    expect(riscv64_hosted_required_marker_fragments()).to_equal(lane.required_serial_markers)
else:
    fail("missing riscv64 hosted lane")
```

</details>

#### routes default RISC-V QEMU targets to fs-backed acceptance lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = get_qemu_target(Architecture.Riscv64)
expect(rv64.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")
expect(rv64.output).to_equal("build/os/simpleos_riscv64_smf_fs.elf")
val rv32 = get_qemu_target(Architecture.Riscv32)
expect(rv32.entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
expect(rv32.output).to_equal("build/os/simpleos_riscv32_smf_fs.elf")
```

</details>

#### defines ARM VirtIO FAT32 SMF execution scenarios

1. fail
   - Expected: arm32.name equals `arm32-virtio-fat32-smf`
   - Expected: arm32.arch equals `Architecture.Arm32`
   - Expected: scenario_test_timeout_ms(arm32) equals `60000`
   - Expected: scenario_lane_kind(arm32) equals `SimpleOsLaneKind.FsExec`
   - Expected: arm32.memory equals `lane.qemu_memory`
   - Expected: arm32.qemu_extra equals `lane.qemu_extra`
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = scenario_arm64_virtio_fat32_smf()
expect(arm64.name).to_equal("arm64-virtio-fat32-smf")
expect(arm64.arch).to_equal(Architecture.Arm64)
expect(arm64.qemu_extra).to_contain("virtio-blk-device,drive=armdisk")
expect(arm64.qemu_extra).to_contain("file=build/os/fat32-arm64.img,if=none,id=armdisk,format=raw")
expect(arm64.qemu_extra).to_contain("-semihosting-config")
expect(scenario_test_timeout_ms(arm64)).to_equal(60000)
expect(scenario_lane_kind(arm64)).to_equal(SimpleOsLaneKind.FsExec)

val arm64_lane = simpleos_platform_qemu_lane("arm64", "arm64-virtio-fat32-smf")
if val lane = arm64_lane:
    expect(arm64.memory).to_equal(lane.qemu_memory)
    expect(arm64.qemu_extra).to_equal(lane.qemu_extra)
else:
    fail("missing arm64 virtio lane")

val arm32 = scenario_arm32_virtio_fat32_smf()
expect(arm32.name).to_equal("arm32-virtio-fat32-smf")
expect(arm32.arch).to_equal(Architecture.Arm32)
expect(arm32.qemu_extra).to_contain("virtio-blk-device,drive=armdisk")
expect(arm32.qemu_extra).to_contain("file=build/os/fat32-arm32.img,if=none,id=armdisk,format=raw")
expect(arm32.qemu_extra).to_contain("-semihosting-config")
expect(scenario_test_timeout_ms(arm32)).to_equal(60000)
expect(scenario_lane_kind(arm32)).to_equal(SimpleOsLaneKind.FsExec)

val arm32_lane = simpleos_platform_qemu_lane("arm32", "arm32-virtio-fat32-smf")
if val lane = arm32_lane:
    expect(arm32.memory).to_equal(lane.qemu_memory)
    expect(arm32.qemu_extra).to_equal(lane.qemu_extra)
else:
    fail("missing arm32 virtio lane")
```

</details>

#### builds QEMU commands with ARM loader and VirtIO block disks

1. fail
   - Expected: arm32_target.entry equals `lane.entry`
   - Expected: arm32_target.linker_script equals `lane.linker_script`
   - Expected: arm32_target.output equals `lane.output`
   - Expected: arm_fs_exec_disk_image_path(Architecture.Arm32) equals `lane.media_path_hint`
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = scenario_arm64_virtio_fat32_smf()
val cmd = build_scenario_command(arm64, "build/os/simpleos_arm64_fs_exec.bin")
expect(cmd[0]).to_equal("qemu-system-aarch64")
expect(cmd).to_contain("loader,file=build/os/simpleos_arm64_fs_exec.bin,addr=0x40200000,force-raw=on")
expect(cmd).to_contain("loader,addr=0x40200000,cpu-num=0")
expect(cmd.contains("-kernel")).to_equal(false)
expect(cmd).to_contain("virtio-blk-device,drive=armdisk")

val target = scenario_target(arm64)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl")
expect(target.linker_script).to_equal("examples/09_embedded/simple_os/arch/arm64/fs_exec_linker.ld")
expect(target.output).to_equal("build/os/simpleos_arm64_fs_exec.elf")

val arm64_lane = simpleos_platform_qemu_lane("arm64", "arm64-virtio-fat32-smf")
if val lane = arm64_lane:
    expect(target.entry).to_equal(lane.entry)
    expect(target.linker_script).to_equal(lane.linker_script)
    expect(target.output).to_equal(lane.output)
    expect(arm_fs_exec_disk_image_path(Architecture.Arm64)).to_equal(lane.media_path_hint)
else:
    fail("missing arm64 virtio lane")

val arm32_target = scenario_target(scenario_arm32_virtio_fat32_smf())
val arm32_lane = simpleos_platform_qemu_lane("arm32", "arm32-virtio-fat32-smf")
if val lane = arm32_lane:
    expect(arm32_target.entry).to_equal(lane.entry)
    expect(arm32_target.linker_script).to_equal(lane.linker_script)
    expect(arm32_target.output).to_equal(lane.output)
    expect(arm_fs_exec_disk_image_path(Architecture.Arm32)).to_equal(lane.media_path_hint)
else:
    fail("missing arm32 virtio lane")
```

</details>

#### looks up ARM SMF scenarios by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scenario_name_or_missing("arm64-virtio-fat32-smf")).to_equal("arm64-virtio-fat32-smf")
expect(scenario_name_or_missing("arm32-virtio-fat32-smf")).to_equal("arm32-virtio-fat32-smf")
expect(arm_fs_exec_disk_image_path(Architecture.Arm64)).to_equal("build/os/fat32-arm64.img")
expect(arm_fs_exec_disk_image_path(Architecture.Arm32)).to_equal("build/os/fat32-arm32.img")
```

</details>

#### dispatches named ARM scenarios through catalog-backed lane kind, serial markers, and media

1. fail
2. fail
   - Expected: scenario_lane_kind(resolved_arm32) equals `SimpleOsLaneKind.FsExec`
   - Expected: scenario_test_timeout_ms(resolved_arm32) equals `60000`
   - Expected: arm_fs_exec_required_marker_fragments(resolved_arm32) equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: arm_fs_exec_disk_image_path(resolved_arm32.arch) equals `resolved_lane.media_path_hint`
3. fail
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = get_scenario("arm64-virtio-fat32-smf")
if val resolved_arm64 = arm64:
    val target = scenario_target(resolved_arm64)
    expect(scenario_lane_kind(resolved_arm64)).to_equal(SimpleOsLaneKind.FsExec)
    expect(scenario_test_timeout_ms(resolved_arm64)).to_equal(60000)
    val lane = simpleos_platform_qemu_lane("arm64", resolved_arm64.name)
    if val resolved_lane = lane:
        expect(arm_fs_exec_required_marker_fragments(resolved_arm64)).to_equal(resolved_lane.required_serial_markers)
        expect(target.entry).to_equal(resolved_lane.entry)
        expect(target.output).to_equal(resolved_lane.output)
        expect(arm_fs_exec_disk_image_path(resolved_arm64.arch)).to_equal(resolved_lane.media_path_hint)
    else:
        fail("missing arm64 virtio lane")
else:
    fail("missing arm64 scenario")

val arm32 = get_scenario("arm32-virtio-fat32-smf")
if val resolved_arm32 = arm32:
    val target = scenario_target(resolved_arm32)
    expect(scenario_lane_kind(resolved_arm32)).to_equal(SimpleOsLaneKind.FsExec)
    expect(scenario_test_timeout_ms(resolved_arm32)).to_equal(60000)
    val lane = simpleos_platform_qemu_lane("arm32", resolved_arm32.name)
    if val resolved_lane = lane:
        expect(arm_fs_exec_required_marker_fragments(resolved_arm32)).to_equal(resolved_lane.required_serial_markers)
        expect(target.entry).to_equal(resolved_lane.entry)
        expect(target.output).to_equal(resolved_lane.output)
        expect(arm_fs_exec_disk_image_path(resolved_arm32.arch)).to_equal(resolved_lane.media_path_hint)
    else:
        fail("missing arm32 virtio lane")
else:
    fail("missing arm32 scenario")
```

</details>

#### defines RISC-V VirtIO FAT32 SMF execution scenarios

1. fail
   - Expected: rv32.name equals `riscv32-virtio-fat32-smf`
   - Expected: rv32.arch equals `Architecture.Riscv32`
   - Expected: scenario_test_timeout_ms(rv32) equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = scenario_riscv64_virtio_fat32_smf()
expect(rv64.name).to_equal("riscv64-virtio-fat32-smf")
expect(rv64.arch).to_equal(Architecture.Riscv64)
expect(rv64.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(rv64.qemu_extra).to_contain("file=build/os/fat32-riscv64.img,if=none,id=rvdisk,format=raw")
expect(scenario_test_timeout_ms(rv64)).to_equal(60000)
expect(scenario_lane_kind(rv64)).to_equal(SimpleOsLaneKind.FsExec)

val rv64_lane = simpleos_platform_qemu_lane("riscv64", "riscv64-virtio-fat32-smf")
if val lane = rv64_lane:
    expect(rv64.memory).to_equal(lane.qemu_memory)
    expect(rv64.qemu_extra).to_equal(lane.qemu_extra[2:])
else:
    fail("missing riscv64 virtio lane")

val rv32 = scenario_riscv32_virtio_fat32_smf()
expect(rv32.name).to_equal("riscv32-virtio-fat32-smf")
expect(rv32.arch).to_equal(Architecture.Riscv32)
expect(rv32.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(rv32.qemu_extra).to_contain("file=build/os/fat32-riscv32.img,if=none,id=rvdisk,format=raw")
expect(scenario_test_timeout_ms(rv32)).to_equal(60000)
```

</details>

#### builds QEMU commands with RISC-V kernels and VirtIO block disks

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = scenario_riscv64_virtio_fat32_smf()
val cmd64 = build_scenario_command(rv64, "build/os/simpleos_riscv64_smf_fs.elf")
expect(cmd64[0]).to_equal("qemu-system-riscv64")
expect(cmd64).to_contain("-kernel")
expect(cmd64).to_contain("build/os/simpleos_riscv64_smf_fs.elf")
expect(cmd64).to_contain("virtio-blk-device,drive=rvdisk")
val target64 = scenario_target(rv64)
expect(target64.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")

val rv32 = scenario_riscv32_virtio_fat32_smf()
val cmd32 = build_scenario_command(rv32, "build/os/simpleos_riscv32_smf_fs.elf")
expect(cmd32[0]).to_equal("qemu-system-riscv32")
expect(cmd32).to_contain("-kernel")
expect(cmd32).to_contain("build/os/simpleos_riscv32_smf_fs.elf")
expect(cmd32).to_contain("virtio-blk-device,drive=rvdisk")
val target32 = scenario_target(rv32)
expect(target32.entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
expect(target32.output).to_equal("build/os/simpleos_riscv32_smf_fs.elf")
```

</details>

#### keeps RV64 media-backed scenario targets aligned with catalog lanes

1. fail
   - Expected: hosted_target.entry equals `lane.entry`
   - Expected: hosted_target.linker_script equals `lane.linker_script`
   - Expected: hosted_target.output equals `lane.output`
   - Expected: riscv_fs_exec_disk_image_path(Architecture.Riscv64) equals `lane.media_path_hint`
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = scenario_riscv64_virtio_fat32_smf()
val rv64_target = scenario_target(rv64)
val rv64_lane = simpleos_platform_qemu_lane("riscv64", "riscv64-virtio-fat32-smf")
if val lane = rv64_lane:
    expect(rv64_target.entry).to_equal(lane.entry)
    expect(rv64_target.linker_script).to_equal(lane.linker_script)
    expect(rv64_target.output).to_equal(lane.output)
    expect(riscv_fs_exec_disk_image_path(Architecture.Riscv64)).to_equal(lane.media_path_hint)
else:
    fail("missing riscv64 virtio lane")

val hosted = scenario_riscv64_hosted()
val hosted_target = scenario_target(hosted)
val hosted_lane = simpleos_platform_qemu_lane("riscv64", "riscv64-hosted")
if val lane = hosted_lane:
    expect(hosted_target.entry).to_equal(lane.entry)
    expect(hosted_target.linker_script).to_equal(lane.linker_script)
    expect(hosted_target.output).to_equal(lane.output)
    expect(riscv_fs_exec_disk_image_path(Architecture.Riscv64)).to_equal(lane.media_path_hint)
else:
    fail("missing riscv64 hosted lane")
```

</details>

#### dispatches named RISC-V scenarios to resolved catalog lanes

1. fail
2. fail
   - Expected: scenario_lane_kind(resolved_hosted) equals `SimpleOsLaneKind.HostedCompileSmoke`
   - Expected: scenario_test_timeout_ms(resolved_hosted) equals `120000`
   - Expected: riscv64_hosted_required_marker_fragments() equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: riscv_fs_exec_disk_image_path(resolved_hosted.arch) equals `resolved_lane.media_path_hint`
3. fail
4. fail
   - Expected: scenario_lane_kind(resolved_rv32) equals `SimpleOsLaneKind.FsExec`
   - Expected: scenario_test_timeout_ms(resolved_rv32) equals `60000`
   - Expected: _scenario_required_marker_fragments(resolved_rv32) equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.linker_script equals `resolved_lane.linker_script`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: riscv_fs_exec_disk_image_path(resolved_rv32.arch) equals `resolved_lane.media_path_hint`
5. fail
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val media = get_scenario("riscv64-virtio-fat32-smf")
if val resolved_media = media:
    val target = scenario_target(resolved_media)
    expect(scenario_lane_kind(resolved_media)).to_equal(SimpleOsLaneKind.FsExec)
    expect(scenario_test_timeout_ms(resolved_media)).to_equal(60000)
    val lane = simpleos_platform_qemu_lane("riscv64", resolved_media.name)
    if val resolved_lane = lane:
        expect(_scenario_required_marker_fragments(resolved_media)).to_equal(resolved_lane.required_serial_markers)
        expect(target.entry).to_equal(resolved_lane.entry)
        expect(target.output).to_equal(resolved_lane.output)
        expect(riscv_fs_exec_disk_image_path(resolved_media.arch)).to_equal(resolved_lane.media_path_hint)
    else:
        fail("missing riscv64 media lane")
else:
    fail("missing riscv64 media scenario")

val hosted = get_scenario("riscv64-hosted")
if val resolved_hosted = hosted:
    val target = scenario_target(resolved_hosted)
    expect(scenario_lane_kind(resolved_hosted)).to_equal(SimpleOsLaneKind.HostedCompileSmoke)
    expect(scenario_test_timeout_ms(resolved_hosted)).to_equal(120000)
    val lane = simpleos_platform_qemu_lane("riscv64", resolved_hosted.name)
    if val resolved_lane = lane:
        expect(riscv64_hosted_required_marker_fragments()).to_equal(resolved_lane.required_serial_markers)
        expect(target.entry).to_equal(resolved_lane.entry)
        expect(target.output).to_equal(resolved_lane.output)
        expect(riscv_fs_exec_disk_image_path(resolved_hosted.arch)).to_equal(resolved_lane.media_path_hint)
    else:
        fail("missing riscv64 hosted lane")
else:
    fail("missing riscv64 hosted scenario")

val rv32 = get_scenario("riscv32-virtio-fat32-smf")
if val resolved_rv32 = rv32:
    val target = scenario_target(resolved_rv32)
    expect(scenario_lane_kind(resolved_rv32)).to_equal(SimpleOsLaneKind.FsExec)
    expect(scenario_test_timeout_ms(resolved_rv32)).to_equal(60000)
    val lane = simpleos_platform_qemu_lane("riscv32", resolved_rv32.name)
    if val resolved_lane = lane:
        expect(_scenario_required_marker_fragments(resolved_rv32)).to_equal(resolved_lane.required_serial_markers)
        expect(target.entry).to_equal(resolved_lane.entry)
        expect(target.linker_script).to_equal(resolved_lane.linker_script)
        expect(target.output).to_equal(resolved_lane.output)
        expect(riscv_fs_exec_disk_image_path(resolved_rv32.arch)).to_equal(resolved_lane.media_path_hint)
    else:
        fail("missing riscv32 media lane")
else:
    fail("missing riscv32 media scenario")
```

</details>

#### scopes RISC-V SMF native builds to arch-local sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64_target = scenario_target(scenario_riscv64_virtio_fat32_smf())
val rv64_args = os_native_build_args(rv64_target, "llvm")
expect(rv64_args).to_contain("--log")
expect(rv64_args).to_contain("on")
expect(rv64_args).to_contain("examples/09_embedded/simple_os/arch/riscv64")
expect(rv64_args.contains("src")).to_equal(false)
expect(os_native_build_sources(rv64_target)[0]).to_equal("build/os/generated")

val rv32_target = scenario_target(scenario_riscv32_virtio_fat32_smf())
val rv32_args = os_native_build_args(rv32_target, "llvm")
expect(rv32_args).to_contain("--log")
expect(rv32_args).to_contain("on")
expect(rv32_args).to_contain("examples/09_embedded/simple_os/arch/riscv32")
expect(rv32_args.contains("src")).to_equal(false)
expect(os_native_build_sources(rv32_target)[0]).to_equal("build/os/generated")
```

</details>

#### lets callers disable compiled OS logging through native-build args

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "off")).to_equal(true)
val x64_target = get_target(Architecture.X86_64)
val x64_args = os_native_build_args(x64_target, "llvm")
expect(x64_args).to_contain("--log")
expect(x64_args).to_contain("off")
expect(os_native_build_sources(x64_target)[0]).to_equal("build/os/generated")
expect(os_native_build_sources(x64_target)).to_contain("src/os")
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "on")).to_equal(true)
```

</details>

#### looks up RISC-V SMF scenarios by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scenario_name_or_missing("riscv64-virtio-fat32-smf")).to_equal("riscv64-virtio-fat32-smf")
expect(scenario_name_or_missing("riscv32-virtio-fat32-smf")).to_equal("riscv32-virtio-fat32-smf")
expect(riscv_fs_exec_disk_image_path(Architecture.Riscv64)).to_equal("build/os/fat32-riscv64.img")
expect(riscv_fs_exec_disk_image_path(Architecture.Riscv32)).to_equal("build/os/fat32-riscv32.img")
```

</details>

#### defines a truthful RV64 hosted preflight scenario

1. fail
   - Expected: hosted_cmd[0] equals `qemu-system-riscv64`
   - Expected: hosted_target.entry equals `examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl`
   - Expected: hosted_target.output equals `build/os/simpleos_riscv64_hosted.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hosted = scenario_riscv64_hosted()
expect(hosted.name).to_equal("riscv64-hosted")
expect(hosted.arch).to_equal(Architecture.Riscv64)
expect(hosted.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(hosted.qemu_extra).to_contain("user,id=n0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80")
expect(hosted.qemu_extra).to_contain("virtio-net-pci,netdev=n0,disable-legacy=on")
expect(scenario_name_or_missing("riscv64-hosted")).to_equal("riscv64-hosted")
expect(scenario_test_timeout_ms(hosted)).to_equal(120000)
expect(scenario_lane_kind(hosted)).to_equal(SimpleOsLaneKind.HostedCompileSmoke)

val hosted_lane = simpleos_platform_qemu_lane("riscv64", "riscv64-hosted")
if val lane = hosted_lane:
    expect(hosted.memory).to_equal(lane.qemu_memory)
    expect(hosted.qemu_extra).to_equal(lane.qemu_extra)
else:
    fail("missing riscv64 hosted lane")

val hosted_cmd = build_scenario_command(hosted, "build/os/simpleos_riscv64_hosted.elf")
expect(hosted_cmd[0]).to_equal("qemu-system-riscv64")
expect(hosted_cmd).to_contain("build/os/simpleos_riscv64_hosted.elf")
expect(hosted_cmd).to_contain("user,id=n0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80")

val hosted_target = scenario_target(hosted)
expect(hosted_target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl")
expect(hosted_target.output).to_equal("build/os/simpleos_riscv64_hosted.elf")
```

</details>

#### uses per-platform x86_64 FAT32 media for filesystem scenarios

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = get_scenario("x64-nvme-fat32")
expect(scenario_name_or_missing("x64-nvme-fat32")).to_equal("x64-nvme-fat32")
if val resolved = scenario:
    val cmd = build_scenario_command(resolved, "build/os/simpleos_fs_test_32.elf")
    expect(cmd).to_contain("file=build/os/fat32-x86_64.img,if=none,id=nvm,format=raw")
```

</details>

#### exposes the q35 pure NVMe perf catalog lane as a runnable x86_64 scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = get_scenario("x86_64-q35-pure-nvme-perf")
expect(scenario_name_or_missing("x86_64-q35-pure-nvme-perf")).to_equal("x86_64-q35-pure-nvme-perf")
if val resolved = scenario:
    expect(scenario_lane_kind(resolved)).to_equal(SimpleOsLaneKind.Smoke)
    expect(scenario_test_timeout_ms(resolved)).to_equal(30000)
    val target = scenario_target(resolved)
    expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/q35_pure_nvme_perf_entry.spl")
    expect(target.output).to_equal("build/os/simpleos_x86_64_pure_nvme_perf.elf")
    val cmd = build_scenario_command(resolved, target.output)
    expect(cmd).to_contain("nvme,id=pureperf,serial=pure-simple-perf")
    expect(cmd).to_contain("file=build/os/fat32-x86_64.img,if=none,id=pureperfns1,format=raw")
    expect(cmd).to_contain("nvme-ns,drive=pureperfns1,bus=pureperf,nsid=1")
    expect(cmd).to_contain("file=build/test-artifacts/simpleos-q35-smoke/q35_user_namespace.img,if=none,id=pureperfns2,format=raw")
    expect(cmd).to_contain("nvme-ns,drive=pureperfns2,bus=pureperf,nsid=2")
    expect(cmd).to_contain("virtio-net-pci,netdev=net0")
else:
    expect("missing").to_equal("x86_64-q35-pure-nvme-perf")
```

</details>

#### delegates physical NVMe perf scenario serial acceptance to the real hardware gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = QemuScenario(
    name: "x86_64-physical-nvme-perf",
    arch: Architecture.X86_64,
    machine: "physical",
    cpu: "physical",
    memory: "",
    qemu_extra: [],
    gui_mode: false,
    description: "physical NVMe serial acceptance gate"
)
val access =
    "[real-device] storage_provider=simple-driver network_provider=simple-driver " +
    "storage_placement=user-space-driver system_storage_placement=system-driver network_placement=user-space-driver " +
    "storage_namespace=non-secure-resource-namespace network_namespace=non-secure-resource-namespace " +
    "storage_grant=resource-grant-set:tok=501 network_grant=resource-grant-set:tok=none common_driver_logic=shared " +
    "user_namespace_assignment=hardware-data-queue user_namespace_mode=user-assigned " +
    "user_namespace_nsid=2 user_namespace_queue_id=2 user_namespace_active_lease_count=1 user_namespace_direct_io=read-write-through user_namespace_shared_interface=fat32,nvfs,dbfs user_namespace_conflict_policy=active-lease-checked\n"
val perf =
    "nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write " +
    "io_size_bytes=4096 direct_io_path=nvme-lease-shared-dma-4k " +
    "fs_consumers=fat32,nvfs,dbfs fat32_direct_io=read-write-through nvfs_direct_io=read-write-through dbfs_direct_io=read-write-through fat32_extent_source=freestanding-fat32-extents " +
    "nvfs_extent_source=freestanding-dbfs-arena dbfs_extent_source=freestanding-dbfs-arena " +
    "c_bridge_used=false c_baseline_device=same-nvme c_baseline_scope=in-guest c_baseline_cache=direct " +
    "common_logic_shared=true " +
    "allocation_per_io=false simple_read_iops=120000 simple_write_iops=90000 " +
    "simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 " +
    "c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 " +
    "queue_depth=64 warm_runs=5 max_rss_kib=32768 hardware_target=real-nvme " +
    "qemu=false device_model=Samsung_PM9A3 device_serial=SN123456 " +
    "namespace_nsid=1 measured_on=real-device\n"
val ready = access + perf + "TEST PASSED\n"
val q35 = access + perf.replace("hardware_target=real-nvme qemu=false", "hardware_target=q35 qemu=true") + "TEST PASSED\n"

expect(qemu_scenario_serial_acceptance_reason(scenario, "", ready)).to_equal("ready")
expect(qemu_scenario_serial_acceptance_reason(scenario, "", q35)).to_equal("missing-physical-nvme-marker:hardware_target=real-nvme")
```

</details>

#### keeps x64 desktop smoke diskless and leaves storage to the disk lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smoke = get_scenario("x64-desktop-test")
expect(scenario_name_or_missing("x64-desktop-test")).to_equal("x64-desktop-test")
if val resolved_smoke = smoke:
    val smoke_cmd = build_scenario_command(resolved_smoke, "build/os/simpleos_desktop_e2e_32.elf")
    expect(command_contains_label(smoke_cmd, "drive=nvm")).to_equal("absent")
    expect(command_contains_label(smoke_cmd, "-vga")).to_equal("present")

val disk = get_scenario("x64-desktop-disk")
expect(scenario_name_or_missing("x64-desktop-disk")).to_equal("x64-desktop-disk")
if val resolved_disk = disk:
    val disk_cmd = build_scenario_command(resolved_disk, "build/os/simpleos_desktop_e2e_32.elf")
    expect(disk_cmd).to_contain("drive=nvm")
    expect(disk_cmd).to_contain("file=build/os/fat32-x86_64.img,if=none,id=nvm,format=raw")
```

</details>

#### defines a UEFI-native x64 desktop disk boot scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_env_set("SIMPLEOS_OVMF_CODE", "build/test-ovmf/OVMF_CODE.fd")).to_equal(true)
expect(ovmf_code_path()).to_equal("build/test-ovmf/OVMF_CODE.fd")
val scenario = scenario_x64_desktop_uefi()
expect(scenario.name).to_equal("x64-desktop-uefi")
expect(scenario.arch).to_equal(Architecture.X86_64)
expect(scenario_test_timeout_ms(scenario)).to_equal(180000)

val resolved = get_scenario("x64-desktop-uefi")
if val s = resolved:
    val cmd = build_scenario_command(s, "build/os/simpleos_desktop_e2e_32.elf")
    expect(cmd[0]).to_equal("qemu-system-x86_64")
    expect(cmd.contains("-kernel")).to_equal(false)
    expect(cmd).to_contain("if=pflash,format=raw,readonly=on,file=build/test-ovmf/OVMF_CODE.fd")
    expect(cmd).to_contain("file=build/os/fat32-x86_64.img,if=none,id=uefidisk,format=raw")
    expect(cmd).to_contain("nvme,serial=uefi-desktop,drive=uefidisk")
else:
    expect("missing").to_equal("x64-desktop-uefi")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Qemu runner serial routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
