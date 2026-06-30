# Simpleos Multiplatform Build Specification

> <details>

<!-- sdn-diagram:id=simpleos_multiplatform_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_multiplatform_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_multiplatform_build_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_multiplatform_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Multiplatform Build Specification

## Scenarios

### SimpleOS multi-platform build catalog

#### exposes 32-bit x86 as a first-class supported target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = simpleos_platform_target_names()
expect(names).to_contain("i686-simpleos")
expect(simpleos_supported_targets()).to_contain("i686-simpleos")
```

</details>

#### records unique QEMU artifact names for all first-class platforms

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = simpleos_platform_target_names()
expect(names.len()).to_equal(6)

expect(simpleos_platform_artifact_slug("x86_64")).to_equal("x86_64")
expect(simpleos_platform_disk_image_output("x86_64")).to_equal("build/os/fat32-x86_64.img")
expect(simpleos_platform_kernel_output("x86_64")).to_equal("build/os/simpleos_x86_64.elf")

expect(simpleos_platform_artifact_slug("x86_32")).to_equal("x86_32")
expect(simpleos_platform_disk_image_output("x86_32")).to_equal("build/os/fat32-x86_32.img")
expect(simpleos_platform_kernel_output("x86_32")).to_equal("build/os/simpleos_x86_32.elf")

expect(simpleos_platform_artifact_slug("arm64")).to_equal("arm64")
expect(simpleos_platform_disk_image_output("arm64")).to_equal("build/os/fat32-arm64.img")
expect(simpleos_platform_kernel_output("arm64")).to_equal("build/os/simpleos_aarch64.elf")

expect(simpleos_platform_artifact_slug("arm32")).to_equal("arm32")
expect(simpleos_platform_disk_image_output("arm32")).to_equal("build/os/fat32-arm32.img")
expect(simpleos_platform_kernel_output("arm32")).to_equal("build/os/simpleos_arm32.elf")

expect(simpleos_platform_artifact_slug("riscv64")).to_equal("riscv64")
expect(simpleos_platform_disk_image_output("riscv64")).to_equal("build/os/fat32-riscv64.img")
expect(simpleos_platform_kernel_output("riscv64")).to_equal("build/os/simpleos_riscv64.elf")

expect(simpleos_platform_artifact_slug("riscv32")).to_equal("riscv32")
expect(simpleos_platform_disk_image_output("riscv32")).to_equal("build/os/fat32-riscv32.img")
expect(simpleos_platform_kernel_output("riscv32")).to_equal("build/os/simpleos_riscv32.elf")
```

</details>

#### exposes QEMU target metadata from the shared platform catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_platform_default_entry("x86_64")).to_equal("examples/09_embedded/simple_os/arch/x86_64/os_entry.spl")
expect(simpleos_platform_linker_script("x86_64")).to_equal("examples/09_embedded/simple_os/arch/x86_64/linker.ld")
expect(simpleos_platform_native_target("x86_64")).to_equal("x86_64-unknown-none")
expect(simpleos_platform_qemu_system("x86_64")).to_equal("qemu-system-x86_64")
expect(simpleos_platform_qemu_machine("x86_64")).to_equal("q35")
expect(simpleos_platform_qemu_cpu("x86_64")).to_equal("qemu64")

expect(simpleos_platform_default_entry("arm32")).to_equal("src/os/kernel/arch/arm32/boot.spl")
expect(simpleos_platform_qemu_system("arm32")).to_equal("qemu-system-arm")
expect(simpleos_platform_qemu_cpu("arm32")).to_equal("cortex-a15")
```

</details>

#### resolves common x86_32 aliases to the i686 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = simpleos_platform_target_by_name("x86_32")
if val resolved = target:
    expect(resolved.name).to_equal("i686-simpleos")
    expect(resolved.arch).to_equal(Architecture.X86)
    expect(resolved.bits).to_equal(32)

val i386 = simpleos_platform_target_by_name("i386")
if val resolved_i386 = i386:
    expect(resolved_i386.name).to_equal("i686-simpleos")
```

</details>

#### uses freestanding i686 flags for 32-bit x86 C and assembly boot inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_flags = simpleos_platform_c_flags("i686-simpleos")
expect(c_flags).to_contain("--target=i686-unknown-none-elf")
expect(c_flags).to_contain("-m32")
expect(c_flags).to_contain("-ffreestanding")
expect(c_flags).to_contain("-DSIMPLEOS_ARCH_X86_32=1")

val asm_flags = simpleos_platform_asm_flags("x86_32")
expect(asm_flags).to_contain("--target=i686-unknown-none-elf")
expect(asm_flags).to_contain("-m32")
```

</details>

#### tracks x86_32 C and assembly boot support sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_sources = simpleos_platform_boot_c_sources("x86_32")
expect(c_sources).to_contain("examples/09_embedded/simple_os/arch/x86_32/boot/baremetal_stubs.c")

val asm_sources = simpleos_platform_boot_asm_sources("x86_32")
expect(asm_sources).to_contain("examples/09_embedded/simple_os/arch/x86_32/boot/crt0.s")
```

</details>

#### records the grandfathered x86_64 native boot backlog separately from entry stubs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backlog = simpleos_platform_grandfathered_native_sources("x86_64")
expect(backlog).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/ap_trampoline.s")
expect(backlog).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/syscall_entry.s")
expect(backlog).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c")
expect(backlog).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c")
```

</details>

#### tracks ARM C and assembly boot support sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64_c_sources = simpleos_platform_boot_c_sources("arm64")
expect(arm64_c_sources).to_contain("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val arm64_asm_sources = simpleos_platform_boot_asm_sources("arm64")
expect(arm64_asm_sources).to_contain("examples/09_embedded/simple_os/arch/arm64/boot/crt0.S")

val arm32_c_sources = simpleos_platform_boot_c_sources("arm32")
expect(arm32_c_sources).to_contain("examples/09_embedded/simple_os/arch/arm32/boot/baremetal_stubs.c")
val arm32_asm_sources = simpleos_platform_boot_asm_sources("arm32")
expect(arm32_asm_sources).to_contain("examples/09_embedded/simple_os/arch/arm32/boot/crt0.s")
```

</details>

#### delegates native SimpleOS target helpers through the platform catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_target_arch("i686-simpleos")).to_equal("x86")
expect(simpleos_clang_target("i686-simpleos")).to_equal("i686-unknown-none-elf")
expect(simpleos_boot_c_sources("i686-simpleos")).to_contain("examples/09_embedded/simple_os/arch/x86_32/boot/baremetal_stubs.c")
expect(simpleos_boot_asm_sources("i686-simpleos")).to_contain("examples/09_embedded/simple_os/arch/x86_32/boot/crt0.s")
expect(simpleos_target_artifact_slug("i686-simpleos")).to_equal("x86_32")
expect(simpleos_target_kernel_output("i686-simpleos")).to_equal("build/os/simpleos_x86_32.elf")
expect(simpleos_target_disk_image_output("i686-simpleos")).to_equal("build/os/fat32-x86_32.img")
```

</details>

#### records riscv32 as RV32IMAC ILP32 soft-float

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = simpleos_platform_target_by_name("riscv32")
if val resolved = target:
    expect(resolved.name).to_equal("riscv32imac-simpleos")
    expect(resolved.bits).to_equal(32)
    expect(resolved.isa).to_equal("rv32imac")
    expect(resolved.abi).to_equal("ilp32")
    expect(resolved.float_abi).to_equal("soft")

val c_flags = simpleos_platform_c_flags("riscv32")
expect(c_flags).to_contain("--target=riscv32-unknown-none-elf")
expect(c_flags).to_contain("-march=rv32imac")
expect(c_flags).to_contain("-mabi=ilp32")
expect(simpleos_platform_isa("riscv32")).to_equal("rv32imac")
expect(simpleos_platform_float_abi("riscv32")).to_equal("soft")
expect(simpleos_platform_needs_soft_float_runtime("riscv32")).to_equal(true)
```

</details>

#### delegates riscv32 ABI helpers through native build config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_target_isa("riscv32imac-simpleos")).to_equal("rv32imac")
expect(simpleos_target_float_abi("riscv32imac-simpleos")).to_equal("soft")
expect(simpleos_target_needs_soft_float_runtime("riscv32imac-simpleos")).to_equal(true)
```

</details>

#### keeps RISC-V SimpleOS boot support in Simple sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_platform_boot_c_sources("riscv64").len()).to_equal(0)
expect(simpleos_platform_boot_asm_sources("riscv64").len()).to_equal(0)
expect(simpleos_boot_c_sources("riscv64gc-simpleos").len()).to_equal(0)
expect(simpleos_boot_asm_sources("riscv64gc-simpleos").len()).to_equal(0)

expect(simpleos_platform_boot_c_sources("riscv32").len()).to_equal(0)
expect(simpleos_platform_boot_asm_sources("riscv32").len()).to_equal(0)
expect(simpleos_boot_c_sources("riscv32imac-simpleos").len()).to_equal(0)
expect(simpleos_boot_asm_sources("riscv32imac-simpleos").len()).to_equal(0)
```

</details>

#### records native-surface policy for primary reduction targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_platform_boot_impl_kind("x86_64")).to_equal(SimpleOsNativeImplementationKind.StandaloneAsm)
expect(simpleos_platform_runtime_impl_kind("x86_64")).to_equal(SimpleOsNativeImplementationKind.Simple)
expect(simpleos_platform_standalone_asm_policy("x86_64")).to_equal(SimpleOsStandaloneAsmPolicy.EntryStubsOnly)

expect(simpleos_platform_boot_impl_kind("riscv64")).to_equal(SimpleOsNativeImplementationKind.EmbeddedAsm)
expect(simpleos_platform_runtime_impl_kind("riscv64")).to_equal(SimpleOsNativeImplementationKind.Simple)
expect(simpleos_platform_standalone_asm_policy("riscv64")).to_equal(SimpleOsStandaloneAsmPolicy.EntryStubsOnly)

expect(simpleos_platform_boot_impl_kind("riscv32")).to_equal(SimpleOsNativeImplementationKind.EmbeddedAsm)
expect(simpleos_platform_runtime_impl_kind("riscv32")).to_equal(SimpleOsNativeImplementationKind.Simple)
expect(simpleos_platform_standalone_asm_policy("riscv32")).to_equal(SimpleOsStandaloneAsmPolicy.EntryStubsOnly)
```

</details>

#### delegates native-surface policy through native build config

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_target_boot_impl_kind("x86_64-simpleos")).to_equal(SimpleOsNativeImplementationKind.StandaloneAsm)
expect(simpleos_target_runtime_impl_kind("x86_64-simpleos")).to_equal(SimpleOsNativeImplementationKind.Simple)
expect(simpleos_target_standalone_asm_policy("x86_64-simpleos")).to_equal(SimpleOsStandaloneAsmPolicy.EntryStubsOnly)
expect(simpleos_target_grandfathered_native_sources("x86_64-simpleos")).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/ap_trampoline.s")

expect(simpleos_target_boot_impl_kind("riscv64gc-simpleos")).to_equal(SimpleOsNativeImplementationKind.EmbeddedAsm)
expect(simpleos_target_standalone_asm_policy("riscv64gc-simpleos")).to_equal(SimpleOsStandaloneAsmPolicy.EntryStubsOnly)
```

</details>

#### records boot firmware, media layout, and staged toolchain contracts

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_platform_firmware_contract("x86_64")).to_equal(SimpleOsFirmwareContractKind.LimineBios)
expect(simpleos_platform_image_layout("x86_64")).to_equal(SimpleOsImageLayoutKind.Fat32Disk)
expect(simpleos_platform_board_adapter_id("x86_64")).to_equal("x86_pc_bios_uefi")

expect(simpleos_platform_firmware_contract("arm64")).to_equal(SimpleOsFirmwareContractKind.RawLoader)
expect(simpleos_platform_image_layout("arm64")).to_equal(SimpleOsImageLayoutKind.VirtioFat32)
expect(simpleos_platform_board_adapter_id("arm64")).to_equal("arm64_u_boot_dtb_sbc")

expect(simpleos_platform_firmware_contract("riscv64")).to_equal(SimpleOsFirmwareContractKind.OpenSbi)
expect(simpleos_platform_image_layout("riscv64")).to_equal(SimpleOsImageLayoutKind.HostedVirtioFat32)
expect(simpleos_platform_board_adapter_id("riscv64")).to_equal("mlk_s02_100t")

expect(simpleos_platform_staged_toolchain_app_names("arm64")).to_equal(["simple_compiler", "simple_loader", "clang", "rust"])
expect(simpleos_platform_staged_toolchain_app_names("riscv64")).to_equal(["simple_compiler", "simple_loader", "llvm", "clang", "rust"])
```

</details>

#### maps acceptance lanes from the catalog instead of separate target tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64_lane = simpleos_platform_qemu_acceptance_lane("arm64")
expect(arm64_lane.name).to_equal("arm64-virtio-fat32-smf")
expect(arm64_lane.lane_kind).to_equal(SimpleOsLaneKind.FsExec)
expect(arm64_lane.entry).to_equal("examples/09_embedded/simple_os/arch/arm64/fs_exec_entry.spl")
expect(arm64_lane.media_path_hint).to_equal("build/os/fat32-arm64.img")

val rv64_lane = simpleos_platform_qemu_acceptance_lane("riscv64")
expect(rv64_lane.name).to_equal("riscv64-hosted")
expect(rv64_lane.lane_kind).to_equal(SimpleOsLaneKind.HostedCompileSmoke)
expect(rv64_lane.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl")
expect(rv64_lane.media_path_hint).to_equal("build/os/fat32-riscv64.img")

val arm_markers = simpleos_platform_qemu_acceptance_required_markers("arm64")
expect(arm_markers).to_contain("[desktop-e2e] process-backed:ok app=simple_compiler pid=")
expect(arm_markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/rust bytes=")
expect(arm_markers).to_contain("TEST PASSED")

val rv64_markers = simpleos_platform_qemu_acceptance_required_markers("riscv64")
expect(rv64_markers).to_contain("[desktop-e2e] native-toolchain-launch:ok app=llvm lane=riscv64-hosted mode=native-filesystem-app status=standalone-required tool=/sys/apps/llvm manifest=/SYS/LLVMMAN.TXT")
expect(rv64_markers).to_contain("HOSTED_FS_TOOLCHAIN_READY arch=riscv64 apps=simple_compiler,simple_loader,llvm,clang,rust")
```

</details>

#### looks up named QEMU lanes without duplicating the x86 smoke lane

1. fail
   - Expected: lane.lane_kind equals `SimpleOsLaneKind.FsExec`
   - Expected: lane.entry equals `examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl`
   - Expected: lane.timeout_ms equals `60000`
   - Expected: lane.media_path_hint equals `build/os/fat32-riscv64.img`
   - Expected: lane.required_serial_markers.len() equals `0`
2. fail
   - Expected: x64_lanes.len() equals `2`
   - Expected: x64_lanes[0].name equals `x86_64-smoke`
   - Expected: x64_lanes[1].name equals `x86_64-q35-pure-nvme-perf`
   - Expected: lane.entry equals `examples/09_embedded/simple_os/arch/x86_64/q35_pure_nvme_perf_entry.spl`
   - Expected: lane.media_path_hint equals `build/os/fat32-x86_64.img`
   - Expected: lane.image_layout equals `SimpleOsImageLayoutKind.Fat32Disk`
   - Expected: lane.output equals `build/os/simpleos_x86_64_pure_nvme_perf.elf`
   - Expected: lane.timeout_ms equals `30000`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64_hosted = simpleos_platform_qemu_lane("riscv64", "riscv64-hosted")
if val lane = rv64_hosted:
    expect(lane.lane_kind).to_equal(SimpleOsLaneKind.HostedCompileSmoke)
    expect(lane.output).to_equal("build/os/simpleos_riscv64_hosted.elf")
else:
    fail("missing riscv64 hosted lane")

val rv64_virtio = simpleos_platform_qemu_lane("riscv64", "riscv64-virtio-fat32-smf")
if val lane = rv64_virtio:
    expect(lane.lane_kind).to_equal(SimpleOsLaneKind.FsExec)
    expect(lane.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")
    expect(lane.timeout_ms).to_equal(60000)
    expect(lane.media_path_hint).to_equal("build/os/fat32-riscv64.img")
    expect(lane.required_serial_markers.len()).to_equal(0)
else:
    fail("missing riscv64 virtio lane")

val x64_lanes = simpleos_platform_qemu_lanes("x86_64")
expect(x64_lanes.len()).to_equal(2)
expect(x64_lanes[0].name).to_equal("x86_64-smoke")
expect(x64_lanes[1].name).to_equal("x86_64-q35-pure-nvme-perf")

val x64_pure = simpleos_platform_qemu_lane("x86_64", "x86_64-q35-pure-nvme-perf")
if val lane = x64_pure:
    expect(lane.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/q35_pure_nvme_perf_entry.spl")
    expect(lane.media_path_hint).to_equal("build/os/fat32-x86_64.img")
    expect(lane.image_layout).to_equal(SimpleOsImageLayoutKind.Fat32Disk)
    expect(lane.output).to_equal("build/os/simpleos_x86_64_pure_nvme_perf.elf")
    expect(lane.timeout_ms).to_equal(30000)
    expect(lane.qemu_extra).to_contain("nvme,id=pureperf,serial=pure-simple-perf")
    expect(lane.qemu_extra).to_contain("file=build/os/fat32-x86_64.img,if=none,id=pureperfns1,format=raw")
    expect(lane.qemu_extra).to_contain("nvme-ns,drive=pureperfns1,bus=pureperf,nsid=1")
    expect(lane.qemu_extra).to_contain("file=build/test-artifacts/simpleos-q35-smoke/q35_user_namespace.img,if=none,id=pureperfns2,format=raw")
    expect(lane.qemu_extra).to_contain("nvme-ns,drive=pureperfns2,bus=pureperf,nsid=2")
    expect(lane.qemu_extra).to_contain("user,id=net0")
    expect(lane.qemu_extra).to_contain("virtio-net-pci,netdev=net0")
    expect(lane.required_serial_markers).to_contain("storage_provider=simple-driver")
    expect(lane.required_serial_markers).to_contain("network_provider=simple-driver")
    expect(lane.required_serial_markers).to_contain("storage_placement=user-space-driver")
    expect(lane.required_serial_markers).to_contain("system_storage_placement=system-driver")
    expect(lane.required_serial_markers).to_contain("network_placement=user-space-driver")
    expect(lane.required_serial_markers).to_contain("storage_namespace=non-secure-resource-namespace")
    expect(lane.required_serial_markers).to_contain("network_namespace=non-secure-resource-namespace")
    expect(lane.required_serial_markers).to_contain("storage_grant=resource-grant-set:tok=")
    expect(lane.required_serial_markers).to_contain("network_grant=resource-grant-set:tok=")
    expect(lane.required_serial_markers).to_contain("common_driver_logic=shared")
    expect(lane.required_serial_markers).to_contain("user_namespace_assignment=hardware-data-queue")
    expect(lane.required_serial_markers).to_contain("user_namespace_mode=user-assigned")
    expect(lane.required_serial_markers).to_contain("user_namespace_queue_id=")
    expect(lane.required_serial_markers).to_contain("user_namespace_direct_io=read-write-through")
    expect(lane.required_serial_markers).to_contain("user_namespace_shared_interface=fat32,nvfs,dbfs")
    expect(lane.required_serial_markers).to_contain("user_namespace_conflict_policy=active-lease-checked")
    expect(lane.required_serial_markers).to_contain("nvme_perf reason=ready")
    expect(lane.required_serial_markers).to_contain("direct_io_path=nvme-lease-shared-dma-4k")
    expect(lane.required_serial_markers).to_contain("fs_consumers=fat32,nvfs,dbfs")
    expect(lane.required_serial_markers).to_contain("fat32_direct_io=read-write-through")
    expect(lane.required_serial_markers).to_contain("nvfs_direct_io=read-write-through")
    expect(lane.required_serial_markers).to_contain("dbfs_direct_io=read-write-through")
    expect(lane.required_serial_markers).to_contain("c_bridge_used=false")
    expect(lane.required_serial_markers).to_contain("allocation_per_io=false")
else:
    fail("missing x86_64 pure nvme perf lane")
```

</details>

#### captures representative board-ready lanes per ISA family

1. fail
   - Expected: resolved_arm64_board.firmware_contract equals `SimpleOsFirmwareContractKind.UBootDtb`
   - Expected: resolved_arm64_board.board_adapter_id equals `arm64_u_boot_dtb_sbc`
2. fail
   - Expected: resolved_rv64_board.board_adapter_id equals `mlk_s02_100t`
3. fail
   - Expected: simpleos_platform_board_lane("arm32") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64_board = simpleos_platform_board_lane("x86_64")
if val resolved_x64_board = x64_board:
    expect(resolved_x64_board.lane_kind).to_equal(SimpleOsLaneKind.BoardCompileSmoke)
    expect(resolved_x64_board.board_adapter_id).to_equal("x86_pc_bios_uefi")
    expect(resolved_x64_board.media_path_hint).to_equal("build/os/fat32-x86_64.img")
else:
    fail("missing x86_64 board lane")

val arm64_board = simpleos_platform_board_lane("arm64")
if val resolved_arm64_board = arm64_board:
    expect(resolved_arm64_board.firmware_contract).to_equal(SimpleOsFirmwareContractKind.UBootDtb)
    expect(resolved_arm64_board.board_adapter_id).to_equal("arm64_u_boot_dtb_sbc")
else:
    fail("missing arm64 board lane")

val rv64_board = simpleos_platform_board_lane("riscv64")
if val resolved_rv64_board = rv64_board:
    expect(resolved_rv64_board.board_adapter_id).to_equal("mlk_s02_100t")
    expect(resolved_rv64_board.media_path_hint).to_contain("generate_riscv_fpga_bundle.spl")
else:
    fail("missing riscv64 board lane")

expect(simpleos_platform_board_lane("arm32")).to_equal(nil)
```

</details>

#### tracks grandfathered non-hal native exceptions for riscv hosted leaves

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64_backlog = simpleos_platform_grandfathered_native_sources("riscv64")
expect(rv64_backlog).to_contain("examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c")
expect(rv64_backlog).to_contain("examples/09_embedded/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c")

val rv32_backlog = simpleos_platform_grandfathered_native_sources("riscv32")
expect(rv32_backlog).to_contain("examples/09_embedded/simple_os/arch/riscv32/boot/baremetal_stubs.c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/simpleos_multiplatform_build_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS multi-platform build catalog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
