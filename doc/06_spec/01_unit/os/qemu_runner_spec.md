# Qemu Runner Specification

> Tests covering Qemu runner serial routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Specification

## Scenarios

### Qemu runner serial routing

#### does not accept non-x86 QEMU exit code 1 as success

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not accept non-x86 QEMU exit code 1 as success
   - Expected: is_qemu_success(arm64, 1) is false
   - Expected: is_qemu_success(arm32, 1) is false
   - Expected: is_qemu_success(rv64, 1) is false
   - Expected: is_qemu_success(arm64, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not accept non-x86 QEMU exit code 1 as success")
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

- keeps isa-debug-exit success limited to x86 scenarios
   - Expected: scenario_qemu_exit_success(x64, 1) is true
   - Expected: scenario_qemu_exit_success(x64, 0) is false
   - Expected: scenario_qemu_exit_success(arm64, 1) is false
   - Expected: scenario_qemu_exit_success(rv64, 1) is false
   - Expected: scenario_qemu_exit_success(arm64, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps isa-debug-exit success limited to x86 scenarios")
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

- exposes a runner-facing protection serial acceptance gate
   - Expected: qemu_protection_serial_accepts_hardening("mps2-an505", "enforce", "qemu", an505_serial) is true
   - Expected: qemu_protection_serial_reason("mps2-an505", "enforce", "none", an505_serial) equals `missing-runtime-check`
   - Expected: qemu_protection_serial_accepts_hardening("mps2-an505", "detect", "qemu", detect_serial) is false
   - Expected: qemu_protection_serial_reason("mps2-an505", "detect", "qemu", detect_serial) equals `diagnostic-protection-mode:detect`
   - Expected: qemu_protection_serial_reason("stm32u585-uno-q", "fault-test", "real-board", fault_missing) equals `missing-fault-recovery`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exposes a runner-facing protection serial acceptance gate")
val an505_serial = "[BOOT] Platform: MPS2-AN505 (QEMU)\n[MPU] Enabled, 8 regions available, 4 configured\nSimpleOS Lite v0.5"
expect(qemu_protection_serial_accepts_hardening("mps2-an505", "enforce", "qemu", an505_serial)).to_equal(true)
expect(qemu_protection_serial_reason("mps2-an505", "enforce", "none", an505_serial)).to_equal("missing-runtime-check")

val detect_serial = "kind=pmsav8-mpu\nprotection_probe=pass\n"
expect(qemu_protection_serial_accepts_hardening("mps2-an505", "detect", "qemu", detect_serial)).to_equal(false)
expect(qemu_protection_serial_reason("mps2-an505", "detect", "qemu", detect_serial)).to_equal("diagnostic-protection-mode:detect")

val fault_missing = "protection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\n"
expect(qemu_protection_serial_reason("stm32u585-uno-q", "fault-test", "real-board", fault_missing)).to_equal("missing-fault-recovery")
```

</details>

#### maps known QEMU scenarios to board protection gates

- maps known QEMU scenarios to board protection gates
   - Expected: qemu_scenario_protection_board_id(x64) equals `x86_64-q35`
   - Expected: qemu_scenario_protection_serial_accepts_hardening(x64, "enforce", x64_serial) is true
   - Expected: qemu_scenario_protection_board_id(rv64) equals `riscv64-virt`
   - Expected: qemu_scenario_protection_serial_accepts_hardening(rv64, "enforce", rv64_serial) is true
   - Expected: qemu_scenario_protection_board_id(arm64) equals ``
   - Expected: qemu_scenario_protection_serial_reason(arm64, "enforce", "protection_probe=pass") equals `unsupported-qemu-board:arm64-virtio-fat32-smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps known QEMU scenarios to board protection gates")
val x64 = scenario_x64_net_user()
val x64_serial = "[BOOT64] call _start\n[harden] text_write_trap=pass\nTEST PASSED"
expect(qemu_scenario_protection_board_id(x64)).to_equal("x86_64-q35")
expect(qemu_scenario_protection_serial_accepts_hardening(x64, "enforce", x64_serial)).to_equal(true)

val rv64 = scenario_riscv64_hosted()
val rv64_serial = "protection_probe=pass\nkind=riscv-sv39\nprotection_enabled=pass\nregion_contract=pass\nsatp_mode=Sv39\nTEST PASSED"
expect(qemu_scenario_protection_board_id(rv64)).to_equal("riscv64-virt")
expect(qemu_scenario_protection_serial_accepts_hardening(rv64, "enforce", rv64_serial)).to_equal(true)

val arm64 = scenario_arm64_virtio_fat32_smf()
expect(qemu_scenario_protection_board_id(arm64)).to_equal("")
expect(qemu_scenario_protection_serial_reason(arm64, "enforce", "protection_probe=pass")).to_equal("unsupported-qemu-board:arm64-virtio-fat32-smf")
```

</details>

#### enumerates 32-bit x86 as a first-class target

- enumerates 32-bit x86 as a first-class target
   - Expected: target.target_triple equals `i686-unknown-none`
   - Expected: target.qemu_system equals `qemu-system-i386`
   - Expected: found_x86_32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("enumerates 32-bit x86 as a first-class target")
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

- launches the x86_32 kernel lane through the compatible QEMU frontend
   - Expected: target.qemu_system equals `qemu-system-i386`
   - Expected: cmd[0] equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("launches the x86_32 kernel lane through the compatible QEMU frontend")
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

- builds normal targets from the shared platform catalog
   - Expected: x86_64.entry equals `examples/09_embedded/simple_os/arch/x86_64/boot_stage1_entry.spl`
   - Expected: x86_64.linker_script equals `examples/09_embedded/simple_os/arch/x86_64/linker.ld`
   - Expected: x86_64.target_triple equals `x86_64-unknown-none`
   - Expected: x86_64.qemu_system equals `qemu-system-x86_64`
   - Expected: arm32.entry equals `src/os/kernel/arch/arm32/boot.spl`
   - Expected: arm32.target_triple equals `armv7-unknown-none-eabihf`
   - Expected: arm32.qemu_system equals `qemu-system-arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds normal targets from the shared platform catalog")
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

- routes default ARM QEMU targets to the fs-exec acceptance lane
   - Expected: arm64.entry equals `examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl`
   - Expected: arm64.output equals `build/os/simpleos_arm64_fs_exec.elf`
   - Expected: arm32.entry equals `examples/09_embedded/simple_os/arch/arm32/fs_exec_entry.spl`
   - Expected: arm32.output equals `build/os/simpleos_arm32_fs_exec.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes default ARM QEMU targets to the fs-exec acceptance lane")
val arm64 = get_qemu_target(Architecture.Arm64)
expect(arm64.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl")
expect(arm64.output).to_equal("build/os/simpleos_arm64_fs_exec.elf")
val arm32 = get_qemu_target(Architecture.Arm32)
expect(arm32.entry).to_equal("examples/09_embedded/simple_os/arch/arm32/fs_exec_entry.spl")
expect(arm32.output).to_equal("build/os/simpleos_arm32_fs_exec.elf")
```

</details>

#### requires four-app fs launch markers for ARM acceptance lanes

- requires four-app fs launch markers for ARM acceptance lanes
   - Expected: markers does not contain `[desktop-e2e] process-backed:ok app=hello_world pid=`
   - Expected: markers does not contain `[desktop-e2e] process-backed:ok app=simple_interpreter pid=`
   - Expected: markers does not contain `[desktop-e2e] process-backed:ok app=llvm pid=`
   - Expected: markers equals `resolved_lane.required_serial_markers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires four-app fs launch markers for ARM acceptance lanes")
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

- keeps ARM and RV64 marker helper surfaces aligned with catalog lanes
   - Expected: arm_fs_exec_required_marker_fragments(scenario_arm64_virtio_fat32_smf()) equals `lane.required_serial_markers`
   - Expected: arm_fs_exec_required_marker_fragments(scenario_arm32_virtio_fat32_smf()) equals `lane.required_serial_markers`
   - Expected: riscv64_hosted_required_marker_fragments() equals `lane.required_serial_markers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps ARM and RV64 marker helper surfaces aligned with catalog lanes")
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

- routes default RISC-V QEMU targets to fs-backed acceptance lanes
   - Expected: rv64.entry equals `examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl`
   - Expected: rv64.output equals `build/os/simpleos_riscv64_smf_fs.elf`
   - Expected: rv32.entry equals `examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl`
   - Expected: rv32.output equals `build/os/simpleos_riscv32_smf_fs.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes default RISC-V QEMU targets to fs-backed acceptance lanes")
val rv64 = get_qemu_target(Architecture.Riscv64)
expect(rv64.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")
expect(rv64.output).to_equal("build/os/simpleos_riscv64_smf_fs.elf")
val rv32 = get_qemu_target(Architecture.Riscv32)
expect(rv32.entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
expect(rv32.output).to_equal("build/os/simpleos_riscv32_smf_fs.elf")
```

</details>

#### defines ARM VirtIO FAT32 SMF execution scenarios

- defines ARM VirtIO FAT32 SMF execution scenarios
   - Expected: arm64.name equals `arm64-virtio-fat32-smf`
   - Expected: arm64.arch equals `Architecture.Arm64`
   - Expected: scenario_test_timeout_ms(arm64) equals `60000`
   - Expected: scenario_lane_kind(arm64) equals `SimpleOsLaneKind.FsExec`
   - Expected: arm64.memory equals `lane.qemu_memory`
   - Expected: arm64.qemu_extra equals `lane.qemu_extra`
   - Expected: arm32.name equals `arm32-virtio-fat32-smf`
   - Expected: arm32.arch equals `Architecture.Arm32`
   - Expected: scenario_test_timeout_ms(arm32) equals `60000`
   - Expected: scenario_lane_kind(arm32) equals `SimpleOsLaneKind.FsExec`
   - Expected: arm32.memory equals `lane.qemu_memory`
   - Expected: arm32.qemu_extra equals `lane.qemu_extra`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines ARM VirtIO FAT32 SMF execution scenarios")
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

- builds QEMU commands with ARM loader and VirtIO block disks
   - Expected: cmd[0] equals `qemu-system-aarch64`
   - Expected: cmd does not contain `-kernel`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl`
   - Expected: target.linker_script equals `examples/09_embedded/simple_os/arch/arm64/fs_exec_linker.ld`
   - Expected: target.output equals `build/os/simpleos_arm64_fs_exec.elf`
   - Expected: target.entry equals `lane.entry`
   - Expected: target.linker_script equals `lane.linker_script`
   - Expected: target.output equals `lane.output`
   - Expected: arm_fs_exec_disk_image_path(Architecture.Arm64) equals `lane.media_path_hint`
   - Expected: arm32_target.entry equals `lane.entry`
   - Expected: arm32_target.linker_script equals `lane.linker_script`
   - Expected: arm32_target.output equals `lane.output`
   - Expected: arm_fs_exec_disk_image_path(Architecture.Arm32) equals `lane.media_path_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds QEMU commands with ARM loader and VirtIO block disks")
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

- looks up ARM SMF scenarios by name
   - Expected: scenario_name_or_missing("arm64-virtio-fat32-smf") equals `arm64-virtio-fat32-smf`
   - Expected: scenario_name_or_missing("arm32-virtio-fat32-smf") equals `arm32-virtio-fat32-smf`
   - Expected: arm_fs_exec_disk_image_path(Architecture.Arm64) equals `build/os/fat32-arm64.img`
   - Expected: arm_fs_exec_disk_image_path(Architecture.Arm32) equals `build/os/fat32-arm32.img`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("looks up ARM SMF scenarios by name")
expect(scenario_name_or_missing("arm64-virtio-fat32-smf")).to_equal("arm64-virtio-fat32-smf")
expect(scenario_name_or_missing("arm32-virtio-fat32-smf")).to_equal("arm32-virtio-fat32-smf")
expect(arm_fs_exec_disk_image_path(Architecture.Arm64)).to_equal("build/os/fat32-arm64.img")
expect(arm_fs_exec_disk_image_path(Architecture.Arm32)).to_equal("build/os/fat32-arm32.img")
```

</details>

#### dispatches named ARM scenarios through catalog-backed lane kind, serial markers, and media

- dispatches named ARM scenarios through catalog-backed lane kind, serial markers, and media
   - Expected: scenario_lane_kind(resolved_arm64) equals `SimpleOsLaneKind.FsExec`
   - Expected: scenario_test_timeout_ms(resolved_arm64) equals `60000`
   - Expected: arm_fs_exec_required_marker_fragments(resolved_arm64) equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: arm_fs_exec_disk_image_path(resolved_arm64.arch) equals `resolved_lane.media_path_hint`
   - Expected: scenario_lane_kind(resolved_arm32) equals `SimpleOsLaneKind.FsExec`
   - Expected: scenario_test_timeout_ms(resolved_arm32) equals `60000`
   - Expected: arm_fs_exec_required_marker_fragments(resolved_arm32) equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: arm_fs_exec_disk_image_path(resolved_arm32.arch) equals `resolved_lane.media_path_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("dispatches named ARM scenarios through catalog-backed lane kind, serial markers, and media")
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

- defines RISC-V VirtIO FAT32 SMF execution scenarios
   - Expected: rv64.name equals `riscv64-virtio-fat32-smf`
   - Expected: rv64.arch equals `Architecture.Riscv64`
   - Expected: scenario_test_timeout_ms(rv64) equals `60000`
   - Expected: scenario_lane_kind(rv64) equals `SimpleOsLaneKind.FsExec`
   - Expected: rv64.memory equals `lane.qemu_memory`
   - Expected: rv64.qemu_extra equals `lane.qemu_extra[2:]`
   - Expected: rv32.name equals `riscv32-virtio-fat32-smf`
   - Expected: rv32.arch equals `Architecture.Riscv32`
   - Expected: scenario_test_timeout_ms(rv32) equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines RISC-V VirtIO FAT32 SMF execution scenarios")
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

- builds QEMU commands with RISC-V kernels and VirtIO block disks
   - Expected: cmd64[0] equals `qemu-system-riscv64`
   - Expected: target64.entry equals `examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl`
   - Expected: cmd32[0] equals `qemu-system-riscv32`
   - Expected: target32.entry equals `examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl`
   - Expected: target32.output equals `build/os/simpleos_riscv32_smf_fs.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds QEMU commands with RISC-V kernels and VirtIO block disks")
val rv64 = scenario_riscv64_virtio_fat32_smf()
val cmd64 = build_scenario_command(rv64, "build/os/simpleos_riscv64_smf_fs.elf")
expect(cmd64[0]).to_equal("qemu-system-riscv64")
# `.claude/rules/board-runnable.md`: RISC-V must boot through the
# OpenSBI real-firmware proxy, never QEMU `-kernel` pass semantics, so
# the same artifact runs on the physical dev board. `-kernel` here is
# only legitimate as the OpenSBI payload handoff, which requires the
# firmware to actually be on the command line.
# RED: `_build_scenario_command_impl` (src/os/_QemuRunner/scenario_exec.spl:417)
# never emits `-bios` — see doc/08_tracking/bug/
# riscv_qemu_lanes_boot_bare_kernel_without_opensbi_2026-08-09.md
expect(cmd64).to_contain("-bios")
expect(cmd64).to_contain("-kernel")
expect(cmd64).to_contain("build/os/simpleos_riscv64_smf_fs.elf")
expect(cmd64).to_contain("virtio-blk-device,drive=rvdisk")
val target64 = scenario_target(rv64)
expect(target64.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")

val rv32 = scenario_riscv32_virtio_fat32_smf()
val cmd32 = build_scenario_command(rv32, "build/os/simpleos_riscv32_smf_fs.elf")
expect(cmd32[0]).to_equal("qemu-system-riscv32")
# Same board-runnable firmware-proxy contract as RV64 above.
expect(cmd32).to_contain("-bios")
expect(cmd32).to_contain("-kernel")
expect(cmd32).to_contain("build/os/simpleos_riscv32_smf_fs.elf")
expect(cmd32).to_contain("virtio-blk-device,drive=rvdisk")
val target32 = scenario_target(rv32)
expect(target32.entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
expect(target32.output).to_equal("build/os/simpleos_riscv32_smf_fs.elf")
```

</details>

#### keeps RV64 media-backed scenario targets aligned with catalog lanes

- keeps RV64 media-backed scenario targets aligned with catalog lanes
   - Expected: rv64_target.entry equals `lane.entry`
   - Expected: rv64_target.linker_script equals `lane.linker_script`
   - Expected: rv64_target.output equals `lane.output`
   - Expected: riscv_fs_exec_disk_image_path(Architecture.Riscv64) equals `lane.media_path_hint`
   - Expected: hosted_target.entry equals `lane.entry`
   - Expected: hosted_target.linker_script equals `lane.linker_script`
   - Expected: hosted_target.output equals `lane.output`
   - Expected: riscv_fs_exec_disk_image_path(Architecture.Riscv64) equals `lane.media_path_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps RV64 media-backed scenario targets aligned with catalog lanes")
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

- dispatches named RISC-V scenarios to resolved catalog lanes
   - Expected: scenario_lane_kind(resolved_media) equals `SimpleOsLaneKind.FsExec`
   - Expected: scenario_test_timeout_ms(resolved_media) equals `60000`
   - Expected: _scenario_required_marker_fragments(resolved_media) equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: riscv_fs_exec_disk_image_path(resolved_media.arch) equals `resolved_lane.media_path_hint`
   - Expected: scenario_lane_kind(resolved_hosted) equals `SimpleOsLaneKind.HostedCompileSmoke`
   - Expected: scenario_test_timeout_ms(resolved_hosted) equals `120000`
   - Expected: riscv64_hosted_required_marker_fragments() equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: riscv_fs_exec_disk_image_path(resolved_hosted.arch) equals `resolved_lane.media_path_hint`
   - Expected: scenario_lane_kind(resolved_rv32) equals `SimpleOsLaneKind.FsExec`
   - Expected: scenario_test_timeout_ms(resolved_rv32) equals `60000`
   - Expected: _scenario_required_marker_fragments(resolved_rv32) equals `resolved_lane.required_serial_markers`
   - Expected: target.entry equals `resolved_lane.entry`
   - Expected: target.linker_script equals `resolved_lane.linker_script`
   - Expected: target.output equals `resolved_lane.output`
   - Expected: riscv_fs_exec_disk_image_path(resolved_rv32.arch) equals `resolved_lane.media_path_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("dispatches named RISC-V scenarios to resolved catalog lanes")
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

- scopes RISC-V SMF native builds to arch-local sources
   - Expected: rv64_args does not contain `src`
   - Expected: os_native_build_sources(rv64_target)[0] equals `build/os/generated`
   - Expected: rv32_args does not contain `src`
   - Expected: os_native_build_sources(rv32_target)[0] equals `build/os/generated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("scopes RISC-V SMF native builds to arch-local sources")
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

#### requires bounded frontend and native-build compiler contracts

- requires bounded frontend and native-build compiler contracts
   - Expected: source does not contain `rt_process_`
   - Expected: source does not contain `rt_file_`
   - Expected: source does not contain `rt_dir_`
   - Expected: source does not contain `rt_env_`
   - Expected: source does not contain `rt_time_`
   - Expected: targets_source does not contain `rt_process_`
   - Expected: targets_source does not contain `rt_file_`
   - Expected: targets_source does not contain `rt_dir_`
   - Expected: targets_source does not contain `rt_env_`
   - Expected: targets_source does not contain `rt_time_`
   - Expected: scenario_source does not contain `rt_`
   - Expected: selector does not contain `src/compiler_rust/target/`
   - Expected: source does not contain `process_run_timeout(simple_bin, args, timeout_ms)`
   - Expected: source does not contain `test/05_perf/io_parity/startup_simple.spl`
   - Expected: source does not contain `frontend_exit_code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 88 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires bounded frontend and native-build compiler contracts")
val source = rt_file_read_text("src/os/_QemuRunner/os_build_run.spl")
val targets_source = rt_file_read_text("src/os/_QemuRunner/runner_targets.spl")
val catalog_source = rt_file_read_text("src/os/_QemuRunner/scenario_catalog.spl")
val disks_source = rt_file_read_text("src/os/_QemuRunner/scenario_disks.spl")
val exec_source = rt_file_read_text("src/os/_QemuRunner/scenario_exec.spl")
expect(source).to_contain("use std.nogc_sync_mut.io.dir_ops.{dir_create_all, dir_remove_all}")
expect(source).to_contain("use std.nogc_sync_mut.io.env_ops.{env_get, env_set, cwd}")
expect(source).to_contain("use std.nogc_sync_mut.io.file_ops.{file_delete, file_exists, file_read}")
expect(source).to_contain("use std.nogc_sync_mut.io.process_ops.{process_run_timeout}")
expect(source).to_contain("use std.nogc_sync_mut.ffi.io.{file_write_text, path_absolute}")
expect(source.contains("rt_process_")).to_equal(false)
expect(source.contains("rt_file_")).to_equal(false)
expect(source.contains("rt_dir_")).to_equal(false)
expect(source.contains("rt_env_")).to_equal(false)
expect(source.contains("rt_time_")).to_equal(false)
expect(targets_source).to_contain("use std.nogc_sync_mut.io.dir_ops.{dir_create_all}")
expect(targets_source).to_contain("use std.nogc_sync_mut.io.env_ops.{env_get}")
expect(targets_source).to_contain("use std.nogc_sync_mut.io.file_ops.{file_exists, file_read}")
expect(targets_source).to_contain("use std.nogc_sync_mut.io.time_ops.{current_time_ms}")
expect(targets_source).to_contain("use std.nogc_sync_mut.ffi.io.{file_write_text}")
expect(targets_source.contains("rt_process_")).to_equal(false)
expect(targets_source.contains("rt_file_")).to_equal(false)
expect(targets_source.contains("rt_dir_")).to_equal(false)
expect(targets_source.contains("rt_env_")).to_equal(false)
expect(targets_source.contains("rt_time_")).to_equal(false)
for scenario_source in [catalog_source, disks_source, exec_source]:
    expect(scenario_source).to_contain("use std.nogc_sync_mut.io.file_ops.{file_exists}")
    expect(scenario_source).to_contain("use std.nogc_sync_mut.io.process_ops.{process_run_timeout}")
    expect(scenario_source.contains("rt_")).to_equal(false)
expect(catalog_source).to_contain("use std.nogc_sync_mut.io.env_ops.{env_get}")
expect(exec_source).to_contain("use std.nogc_sync_mut.io.dir_ops.{dir_create_all}")
expect(exec_source).to_contain("use std.nogc_sync_mut.io.env_ops.{env_get}")
val start = source.find("fn _find_simple_binary_for_target")
expect(start).to_be_greater_than(-1)
val selector = source.slice(start, source.len())
val explicit = selector.find("val env_bin = env_get(\"SIMPLE_BINARY\")")
val explicit_alias = selector.find("val env_simple_bin = env_get(\"SIMPLE_BIN\")")
expect(explicit).to_be_greater_than(-1)
expect(explicit_alias).to_be_greater_than(explicit)
expect(selector.contains("src/compiler_rust/target/")).to_equal(false)
expect(source).to_contain("if _simple_binary_has_native_build_contract(cand, backend_name):\n            return cand\n    \"\"\n\nfn _build_sources")
expect(source).to_contain("fn _run_candidate_pinned(candidate: text, args: [text], timeout_ms: i64)")
expect(source).to_contain("fn _run_candidate_admission_pinned(candidate: text, args: [text], timeout_ms: i64)")
expect(source).to_contain("fn _candidate_frontend_smoke(candidate: text) -> bool:")
expect(source).to_contain("process_run_timeout(\"env\", command_args, timeout_ms)")
expect(source).to_contain("var pinned_candidate = path_absolute(candidate)")
expect(source).to_contain("pinned_candidate = candidate")
expect(source).to_contain("SIMPLE_BINARY={pinned_candidate}")
expect(source).to_contain("SIMPLE_BIN={pinned_candidate}")
expect(source).to_contain("SIMPLE_BOOTSTRAP_DRIVER={pinned_candidate}")
expect(source).to_contain("SIMPLE_FRONTEND_DELEGATE={pinned_candidate}")
expect(source).to_contain("SIMPLE_FRONTEND_DELEGATED=1")
expect(source).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
expect(source).to_contain("SIMPLE_EXECUTION_MODE=")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_FORCE_WORKER=0")
expect(source).to_contain("SIMPLE_BOOTSTRAP=0")
expect(source).to_contain("simpleos-qemu-admission.")
expect(source).to_contain("var temp_root = env_get(\"TMPDIR\") ?? \"\"")
expect(source).to_contain("scripts/check/cert/redeploy_gate/fixtures/p2_add.spl")
expect(source).to_contain("\"--runtime-bundle\", \"core-c-bootstrap\"")
expect(source).to_contain("\"--entry-closure\"")
expect(source).to_contain("\"--cache-dir\", probe_dir + \"/cache\"")
expect(source).to_contain("\"--mode\", \"one-binary\"")
expect(source).to_contain("candidate, build_args, 60000")
expect(source).to_contain("process_run_timeout(probe_output, [], 5000)")
expect(source).to_contain("stdout == \"5\" or stdout == \"5\\n\" or stdout == \"5\\r\\n\"")
expect(source).to_contain("val cleanup_ok = dir_remove_all(probe_dir)")
expect(source).to_contain("_candidate_frontend_smoke(candidate)")
expect(source).to_contain("_run_candidate_admission_pinned(candidate, probe_args, 5000)")
expect(source).to_contain("_run_candidate_pinned(simple_bin, args, timeout_ms)")
expect(source.contains("process_run_timeout(simple_bin, args, timeout_ms)")).to_equal(false)
expect(source).to_contain("env_set(\"SIMPLE_BOOTSTRAP\", old_bootstrap)")
expect(source).to_contain("env_set(\"SIMPLE_LIB\", old_lib)")
expect(source).to_contain("env_set(\"SIMPLE_BOOT_MINIMAL\", old_boot_minimal)")
expect(source).to_contain("env_set(\"SIMPLE_ALLOW_FREESTANDING_STUBS\", old_stub_env)")
expect(source).to_contain("env_set(\"SIMPLE_NO_STUB_FALLBACK\", old_no_stub_fallback)")
expect(source).to_contain("env_set(\"SIMPLE_OS_LOG_MODE\", old_log_mode)")
expect(source).to_contain("env_set(\"PATH\", old_path)")
expect(source).to_contain("env_set(\"SIMPLE_SSH_LIVE_BUILD_MARKER\", old_build_marker)")
expect(source.contains("test/05_perf/io_parity/startup_simple.spl")).to_equal(false)
expect(source.contains("frontend_exit_code")).to_equal(false)
expect(source).to_contain("\"--backend\", backend_name")
expect(source).to_contain("\"--mode\", \"definitely-invalid-mode\"")
expect(source).to_contain("exit_code == 1 and (stdout + \"\\n\" + stderr).contains(diagnostic)")
expect(source).to_contain("if simple_bin == \"\":\n        _remove_stale_build_output(target)")
expect(source).to_contain("phase=tooling FAILED: no runnable pure-Simple compiler")
```

</details>

#### lets callers disable compiled OS logging through native-build args

- lets callers disable compiled OS logging through native-build args
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "off") is true
   - Expected: os_native_build_sources(x64_target)[0] equals `build/os/generated`
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", "on") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("lets callers disable compiled OS logging through native-build args")
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "off")).to_equal(true)
val x64_target = get_target(Architecture.X86_64)
val x64_args = os_native_build_args(x64_target, "llvm")
expect(x64_args).to_contain("--log")
expect(x64_args).to_contain("off")
expect(os_native_build_sources(x64_target)[0]).to_equal("build/os/generated")
expect(os_native_build_sources(x64_target)).to_contain("src")
expect(rt_env_set("SIMPLE_OS_LOG_MODE", "on")).to_equal(true)
```

</details>

#### bounds wm simple web worker timeout below the OS build timeout

- bounds wm simple web worker timeout below the OS build timeout
   - Expected: default_os_build_backend_for_target(target) equals `llvm`
   - Expected: os_native_build_sources(target) equals `["examples/09_embedded/simple_os/arch/x86_64"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("bounds wm simple web worker timeout below the OS build timeout")
val target = get_wm_simple_web_check_target()
expect(default_os_build_backend_for_target(target)).to_equal("llvm")
val args = os_native_build_args(target, "llvm")
expect(args).to_contain("--timeout")
expect(args).to_contain("870")
expect(args).to_contain("--opt-level=none")
expect(os_native_build_sources(target)).to_equal(["examples/09_embedded/simple_os/arch/x86_64"])
```

</details>

<details>
<summary>Advanced: gives SSH live builds the same cold-build worker timeout headroom</summary>

#### gives SSH live builds the same cold-build worker timeout headroom

- gives SSH live builds the same cold-build worker timeout headroom
   - Expected: rt_env_set("SIMPLE_OS_BUILD_TIMEOUT_MS", "120000") is true
   - Expected: rt_env_set("SIMPLE_OS_BUILD_TIMEOUT_MS", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gives SSH live builds the same cold-build worker timeout headroom")
val target = get_ssh_live_target()
val args = os_native_build_args(target, "cranelift")
expect(args).to_contain("--timeout")
expect(args).to_contain("870")
expect(rt_env_set("SIMPLE_OS_BUILD_TIMEOUT_MS", "120000")).to_equal(true)
val short_args = os_native_build_args(target, "cranelift")
expect(short_args).to_contain("--timeout")
expect(short_args).to_contain("119")
expect(rt_env_set("SIMPLE_OS_BUILD_TIMEOUT_MS", "")).to_equal(true)
```

</details>


</details>

#### looks up RISC-V SMF scenarios by name

- looks up RISC-V SMF scenarios by name
   - Expected: scenario_name_or_missing("riscv64-virtio-fat32-smf") equals `riscv64-virtio-fat32-smf`
   - Expected: scenario_name_or_missing("riscv32-virtio-fat32-smf") equals `riscv32-virtio-fat32-smf`
   - Expected: riscv_fs_exec_disk_image_path(Architecture.Riscv64) equals `build/os/fat32-riscv64.img`
   - Expected: riscv_fs_exec_disk_image_path(Architecture.Riscv32) equals `build/os/fat32-riscv32.img`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("looks up RISC-V SMF scenarios by name")
expect(scenario_name_or_missing("riscv64-virtio-fat32-smf")).to_equal("riscv64-virtio-fat32-smf")
expect(scenario_name_or_missing("riscv32-virtio-fat32-smf")).to_equal("riscv32-virtio-fat32-smf")
expect(riscv_fs_exec_disk_image_path(Architecture.Riscv64)).to_equal("build/os/fat32-riscv64.img")
expect(riscv_fs_exec_disk_image_path(Architecture.Riscv32)).to_equal("build/os/fat32-riscv32.img")
```

</details>

#### defines a truthful RV64 hosted preflight scenario

- defines a truthful RV64 hosted preflight scenario
   - Expected: hosted.name equals `riscv64-hosted`
   - Expected: hosted.arch equals `Architecture.Riscv64`
   - Expected: scenario_name_or_missing("riscv64-hosted") equals `riscv64-hosted`
   - Expected: scenario_test_timeout_ms(hosted) equals `120000`
   - Expected: scenario_lane_kind(hosted) equals `SimpleOsLaneKind.HostedCompileSmoke`
   - Expected: hosted.memory equals `lane.qemu_memory`
   - Expected: hosted.qemu_extra equals `lane.qemu_extra`
   - Expected: hosted_cmd[0] equals `qemu-system-riscv64`
   - Expected: hosted_target.entry equals `examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl`
   - Expected: hosted_target.output equals `build/os/simpleos_riscv64_hosted.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines a truthful RV64 hosted preflight scenario")
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

#### defines an RV64 X25519 diagnostic lane with live helper build inputs

- defines an RV64 X25519 diagnostic lane with live helper build inputs
   - Expected: probe.name equals `rv64-x25519-probe`
   - Expected: probe.arch equals `Architecture.Riscv64`
   - Expected: scenario_name_or_missing("rv64-x25519-probe") equals `rv64-x25519-probe`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/riscv64/x25519_probe_entry.spl`
   - Expected: target.output equals `build/os/simpleos_riscv64_x25519_probe.elf`
   - Expected: default_os_build_backend_for_target(target) equals `cranelift`
   - Expected: os_native_build_sources(target) equals `["build/os/generated", "src", "examples"]`
   - Expected: cmd[0] equals `qemu-system-riscv64`
   - Expected: scenario_qemu_exit_success(probe, 124) is true
   - Expected: scenario_qemu_exit_success(probe, -1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines an RV64 X25519 diagnostic lane with live helper build inputs")
val probe = scenario_rv64_x25519_probe()
expect(probe.name).to_equal("rv64-x25519-probe")
expect(probe.arch).to_equal(Architecture.Riscv64)
expect(scenario_name_or_missing("rv64-x25519-probe")).to_equal("rv64-x25519-probe")

val target = scenario_target(probe)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/x25519_probe_entry.spl")
expect(target.output).to_equal("build/os/simpleos_riscv64_x25519_probe.elf")
expect(default_os_build_backend_for_target(target)).to_equal("cranelift")
expect(os_native_build_sources(target)).to_equal(["build/os/generated", "src", "examples"])
expect(os_native_build_args(target, "cranelift")).to_contain("--timeout")
expect(os_native_build_args(target, "cranelift")).to_contain("180")
expect(os_native_build_env_prefix(target, "")).to_contain("SIMPLE_BOOT_MINIMAL=1")

val cmd = build_scenario_command(probe, target.output)
expect(cmd[0]).to_equal("qemu-system-riscv64")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_riscv64_x25519_probe.elf")
expect(scenario_qemu_exit_success(probe, 124)).to_equal(true)
expect(scenario_qemu_exit_success(probe, -1)).to_equal(true)
```

</details>

#### uses per-platform x86_64 FAT32 media for filesystem scenarios

- uses per-platform x86_64 FAT32 media for filesystem scenarios
   - Expected: scenario_name_or_missing("x64-nvme-fat32") equals `x64-nvme-fat32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses per-platform x86_64 FAT32 media for filesystem scenarios")
val scenario = get_scenario("x64-nvme-fat32")
expect(scenario_name_or_missing("x64-nvme-fat32")).to_equal("x64-nvme-fat32")
if val resolved = scenario:
    val cmd = build_scenario_command(resolved, "build/os/simpleos_fs_test_32.elf")
    expect(cmd).to_contain("file=build/os/fat32-x86_64.img,if=none,id=nvm,format=raw")
```

</details>

#### exposes the q35 pure NVMe perf catalog lane as a runnable x86_64 scenario

- exposes the q35 pure NVMe perf catalog lane as a runnable x86_64 scenario
   - Expected: scenario_name_or_missing("x86_64-q35-pure-nvme-perf") equals `x86_64-q35-pure-nvme-perf`
   - Expected: scenario_lane_kind(resolved) equals `SimpleOsLaneKind.Smoke`
   - Expected: scenario_test_timeout_ms(resolved) equals `30000`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/x86_64/q35_pure_nvme_perf_entry.spl`
   - Expected: target.output equals `build/os/simpleos_x86_64_pure_nvme_perf.elf`
   - Expected: "missing" equals `x86_64-q35-pure-nvme-perf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exposes the q35 pure NVMe perf catalog lane as a runnable x86_64 scenario")
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

#### routes the x64 GPU 2D scenario to the virtio-gpu test target

- routes the x64 GPU 2D scenario to the virtio-gpu test target
   - Expected: scenario_name_or_missing("x64-gpu-2d") equals `x64-gpu-2d`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/x86_64/gpu_test_entry.spl`
   - Expected: target.output equals `build/os/simpleos_gpu_test_x86_64.elf`
   - Expected: os_native_build_sources(target) equals `["build/os/generated", "src/os", "src/lib", "examples/09_embedded/simple_os"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes the x64 GPU 2D scenario to the virtio-gpu test target")
val scenario = scenario_x64_gpu_2d()
expect(scenario_name_or_missing("x64-gpu-2d")).to_equal("x64-gpu-2d")
val target = scenario_target(scenario)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/gpu_test_entry.spl")
expect(target.output).to_equal("build/os/simpleos_gpu_test_x86_64.elf")
expect(os_native_build_sources(target)).to_equal(["build/os/generated", "src/os", "src/lib", "examples/09_embedded/simple_os"])
expect(os_native_build_env_prefix(target, "")).to_contain("SIMPLE_BOOTSTRAP=1")
expect(os_native_build_env_prefix(target, "")).to_contain("SIMPLE_ALLOW_FREESTANDING_STUBS=1")
val cmd = build_scenario_command(scenario, target.output)
expect(cmd).to_contain("virtio-gpu,disable-modern=on,disable-legacy=off")
expect(cmd).to_contain("-vga")
expect(cmd).to_contain("none")
```

</details>

#### delegates physical NVMe perf scenario serial acceptance to the real hardware gate

- delegates physical NVMe perf scenario serial acceptance to the real hardware gate
   - Expected: qemu_scenario_serial_acceptance_reason(scenario, "", ready) equals `ready`
   - Expected: qemu_scenario_serial_acceptance_reason(scenario, "", q35) equals `missing-physical-nvme-marker:hardware_target=real-nvme`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("delegates physical NVMe perf scenario serial acceptance to the real hardware gate")
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
    "vfat_baseline_device=same-nvme vfat_baseline_scope=in-guest vfat_baseline_cache=direct vfat_baseline_filesystem=vfat " +
    "common_logic_shared=true " +
    "allocation_per_io=false simple_read_iops=120000 simple_write_iops=90000 " +
    "simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 " +
    "c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 " +
    "queue_depth=64 warm_runs=5 max_rss_kib=32768 hardware_target=real-nvme " +
    "qemu=false physical_runs=5 device_model=Samsung_PM9A3 device_serial=SN123456 " +
    "namespace_nsid=1 measured_on=real-device\n"
val ready = access + perf + "TEST PASSED\n"
val q35 = access + perf.replace("hardware_target=real-nvme qemu=false", "hardware_target=q35 qemu=true") + "TEST PASSED\n"

expect(qemu_scenario_serial_acceptance_reason(scenario, "", ready)).to_equal("ready")
expect(qemu_scenario_serial_acceptance_reason(scenario, "", q35)).to_equal("missing-physical-nvme-marker:hardware_target=real-nvme")
```

</details>

#### keeps x64 desktop smoke diskless and leaves storage to the disk lane

- keeps x64 desktop smoke diskless and leaves storage to the disk lane
   - Expected: scenario_name_or_missing("x64-desktop-test") equals `x64-desktop-test`
   - Expected: command_contains_label(smoke_cmd, "drive=nvm") equals `absent`
   - Expected: command_contains_label(smoke_cmd, "-vga") equals `present`
   - Expected: scenario_name_or_missing("x64-desktop-disk") equals `x64-desktop-disk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps x64 desktop smoke diskless and leaves storage to the disk lane")
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
    expect(disk_cmd).to_contain("nvme,serial=deadbeef,drive=nvm")
    expect(disk_cmd).to_contain("file=build/os/fat32-x86_64.img,if=none,id=nvm,format=raw")
```

</details>

#### defines a UEFI-native x64 desktop disk boot scenario

- defines a UEFI-native x64 desktop disk boot scenario
   - Expected: rt_env_set("SIMPLEOS_OVMF_CODE", "build/test-ovmf/OVMF_CODE.fd") is true
   - Expected: ovmf_code_path() equals `build/test-ovmf/OVMF_CODE.fd`
   - Expected: scenario.name equals `x64-desktop-uefi`
   - Expected: scenario.arch equals `Architecture.X86_64`
   - Expected: scenario_test_timeout_ms(scenario) equals `180000`
   - Expected: cmd[0] equals `qemu-system-x86_64`
   - Expected: cmd does not contain `-kernel`
   - Expected: "missing" equals `x64-desktop-uefi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines a UEFI-native x64 desktop disk boot scenario")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Qemu runner serial routing.
- Qemu runner serial routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80574c395d2a6f55e2fadbbf5ddca1af40c5c90a99f9cbc2f8f111dc15a006f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80574c395d2a6f55e2fadbbf5ddca1af40c5c90a99f9cbc2f8f111dc15a006f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80574c395d2a6f55e2fadbbf5ddca1af40c5c90a99f9cbc2f8f111dc15a006f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/qemu_runner_spec.spl
mirror: doc/06_spec/01_unit/os/qemu_runner_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/qemu_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/qemu_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/qemu_runner_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/qemu_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/qemu_runner_spec.spl:207:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not accept non-x86 QEMU exit code 1 as success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/qemu_runner_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps isa-debug-exit success limited to x86 scenarios' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/qemu_runner_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes a runner-facing protection serial acceptance gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
