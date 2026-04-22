# SimpleOS Platform Feature Matrix

Last updated: 2026-04-22

This file tracks SimpleOS "full OS" parity by small feature rows. The goal is
to separate shared kernel logic from platform-specific proof work, so a target
is not called complete just because it has a boot target or a hosted unit test.

Status legend:

| Mark | Meaning |
|------|---------|
| I | Implemented in source or target metadata exists |
| V | Verified by focused unit/system test or live QEMU lane |
| P | Partial: modeled, hosted-only, gated, or missing live proof |
| B | Blocked by toolchain, QEMU lane, or boot/runtime prerequisite |
| N | Not implemented or no evidence found |
| NA | Not applicable |

Platform columns use `impl/verified`.

| ID | Low Feature | Shared Logic | Shared Owner | x86_64 | x86_32 | arm64 | arm32 | riscv64 | riscv32 | Verification Evidence / Gap |
|----|-------------|--------------|--------------|--------|--------|-------|-------|---------|---------|-----------------------------|
| OS-BOOT-001 | Architecture enum and target lookup | Yes | `arch_context`, `qemu_runner`, `simpleos_multiplatform_build` | I/V | I/V | I/V | I/V | I/V | I/V | `boot_smoke_spec.spl` and qemu runner specs cover platform target registration; ARM/RISC-V also have QEMU boot spec files. |
| OS-BOOT-002 | Architecture aliases and display names | Yes | `qemu_runner.arch_from_name` | I/V | I/V | I/V | I/V | I/V | I/V | Aliases include x86_32/i386/i686, arm64/aarch64, arm32/armv7, rv64/riscv64, and rv32/riscv32 paths. |
| OS-BOOT-003 | Kernel entry source and linker script | Platform | `src/os/kernel/arch/*/boot.spl`, `linker.ld` | I/V | I/V | I/V | I/V | I/V | I/V | Metadata exists for all six lanes; live proof differs by target and scenario. |
| OS-BOOT-004 | QEMU command construction | Shared + platform options | `qemu_runner.build_qemu_command` | I/V | I/V | I/V | I/V | I/V | I/V | x86_32 command verifies `qemu-system-i386`, `pc`, `qemu32`, `128M`; ARM/RISC-V scenario specs cover their registered lanes. |
| OS-BOOT-005 | Live serial boot marker | Platform | QEMU live specs | I/V | P/B | I/P | I/V | I/V | I/V | x86_32 gated live spec exists but true live boot is blocked by i686 backend support; arm32/riscv boot specs and RISC-V SMF serial markers exist. |
| OS-BOOT-006 | Debug-exit / deterministic QEMU exit | Platform | QEMU target extras | I/V | P/B | P | P | P | P | x86_32 acceptance requires `isa-debug-exit`; not live-proven. |
| OS-BOOT-007 | Disk/firmware boot lane | Platform | QEMU scenarios | I/V | N | P | P | P | P | x86_64 has OVMF/disk desktop lanes; x86_32 has no disk boot acceptance lane. |
| OS-HAL-001 | HAL aggregate type | Shared shape, platform structs | `arch/*/mod.spl` | I/P | I/P | I/P | I/P | I/P | I/P | Each platform exposes `create_*_hal`; parity-level behavioral tests are incomplete. |
| OS-HAL-002 | Serial console primitive | Platform | `arch/*/console.spl` | I/P | I/P | I/P | I/P | I/P | I/P | x86_32 COM1 console exists; live serial proof is boot-blocked. |
| OS-HAL-003 | CPU interrupt enable/disable | Platform | `arch/*/cpu.spl` | I/P | I/P | I/P | I/P | I/P | I/P | Source exists for x86_32 CPU primitives; live interrupt behavior not proven. |
| OS-HAL-004 | Descriptor/trap table install | Platform | `arch/*/interrupt.spl` | I/V | P/V | P | P | P | P | x86_32 hosted runtime bridge verified; actual i386 IDT gate and assembly entry missing. |
| OS-HAL-005 | Timer initialization | Platform | `arch/*/timer.spl` | I/P | I/P | I/P | I/P | I/P | I/P | x86_32 PIT module exists; live timer/preemption proof missing. |
| OS-MEM-001 | Page-size contract | Shared + platform | paging modules | I/P | I/P | I/P | I/P | I/P | I/P | x86_32 paging exposes 4 KiB / 2-level model; contract tests should be broadened. |
| OS-MEM-002 | User address-space creation | Shared | `user_address_space`, `vmm` | I/P | I/P | I/P | I/P | I/P | I/P | Scheduler maps synthetic roots in hosted tests; live per-platform page table activation is uneven. |
| OS-MEM-003 | PT_LOAD segment mapping | Shared | `segment_mapper.map_all` | I/V | I/V | I/P | I/P | I/P | I/P | x86_32 now reaches shared process-image load plan; live mapping not proven. |
| OS-MEM-004 | Initial user stack mapping | Shared | `segment_mapper.map_stack`, `stack_builder` | I/V | I/V | I/P | I/P | I/P | I/P | x86_32 has `X86_32_USER_STACK_TOP` and process-image unit coverage. |
| OS-MEM-005 | brk model | Shared syscall + VMM | `ipc/syscall.spl` | I/V | I/V | I/V | I/V | I/V | I/V | Shared unit tests cover brk; x86_32 trap bridge now covers `brk(0)` hosted. Live x86_32 brk missing. |
| OS-EXEC-001 | ELF class and machine validation | Shared | `loader/elf_loader.spl` | I/V | I/V | I/V | I/V | I/V | I/V | x86_32 ELF32/i386 admission added and tested. |
| OS-EXEC-002 | SMF wrapper extraction | Shared | `loader/smf.spl`, `process_image.spl` | I/V | I/P | I/P | I/P | I/P | I/P | x86_32 native ELF is tested; x86_32 SMF handoff still needs explicit coverage. |
| OS-EXEC-003 | Process image construction | Shared | `loader/process_image.spl` | I/V | I/V | I/P | I/P | I/P | I/P | x86_32 minimal ELF image creates entry, stack, segment plan. |
| OS-EXEC-004 | Architecture-specific user stack top | Shared selector + constants | `process_image.spl` | I/V | I/V | I/V | I/V | I/V | I/V | x86_32 stack top is `0xBFFFF000`. |
| OS-EXEC-005 | Scheduler user context construction | Shared switch + arch branches | `scheduler_user_context_for_arch` | I/V | I/V | I/V | I/V | I/P | I/P | x86_32 explicit branch verifies `rip`, aligned stack, `cs=0x1B`, `ss=0x23`. |
| OS-EXEC-006 | Process-backed task creation from image | Shared | `Scheduler.create_user_task_pid` | I/V | I/V | I/P | I/P | I/P | I/P | x86_32 arch-param syscall handoff proves process-backed task in hosted tests. |
| OS-EXEC-007 | execve-style replacement | Shared syscall + scheduler | `_handle_exec`, `Scheduler.exec_image` | I/V | P | P | P | P | P | x86_32 process image is ready, but live `exec` on x86_32 is not proven. |
| OS-EXEC-008 | spawn binary from path bytes | Shared syscall + source resolver | `dispatch_spawn_binary_direct` | I/V | I/V | I/P | I/P | I/P | I/P | x86_32 arch-param handoff covers resolved bytes; compile-time x86 live path not proven. |
| OS-EXEC-009 | Filesystem-backed app execution | Shared + media | VFS/FAT32/NVMe/VirtIO lanes | I/V | N | I/P | I/P | I/V | I/P | RISC-V SMF/fs launch specs and rv64 shared-service markers exist; x86_32 has no FAT32/NVMe or equivalent QEMU app-exec lane. |
| OS-SYSCALL-001 | Portable syscall argument/result structs | Yes | `types/syscall_types.spl` | I/V | I/V | I/V | I/V | I/V | I/V | Shared handler used by x86_32 hosted trap bridge. |
| OS-SYSCALL-002 | x86_64 syscall register model | Platform | `arch/x86_64/interrupt.spl` | I/V | NA | NA | NA | NA | NA | Full x86_64 lane owns current desktop/syscall smoke. |
| OS-SYSCALL-003 | x86_32 int 0x80 register model | Platform but pure logic | `arch/x86_32/trap_model.spl` | NA | I/V | NA | NA | NA | NA | `eax` id/result, `ebx/ecx/edx/esi/edi/ebp` args, `eip += 2`. |
| OS-SYSCALL-004 | x86_32 hosted trap dispatch | Platform bridge + shared handler | `arch/x86_32/interrupt.spl` | NA | I/V | NA | NA | NA | NA | getpid, brk, primitive ABI covered. |
| OS-SYSCALL-005 | x86_32 live int 0x80 gate | Platform assembly/runtime | IDT gate + save/restore stub | NA | N/B | NA | NA | NA | NA | Required before x86_32 can be full OS lane. |
| OS-SYSCALL-006 | RISC-V ecall register model | Platform | RISC-V trap path | NA | NA | NA | NA | I/V | P | RV64 trap model specs cover ecall classification, register mapping, and result application; RV32 needs equivalent explicit syscall model coverage. |
| OS-SYSCALL-007 | ARM SVC/exception syscall model | Platform | ARM trap path | NA | NA | P | P | NA | NA | ARM fs-exec lanes exist but syscall parity evidence is partial. |
| OS-SCHED-001 | Task table and ready queues | Shared | `scheduler.spl` | I/V | I/V | I/V | I/V | I/V | I/V | Scheduler specs cover core behavior independent of target. |
| OS-SCHED-002 | Process diagnostics task listing | Shared syscall | `syscall_handler id=5` | I/V | P | P | P | P | P | Shared unit coverage exists; x86_32 trap/live diagnostics not complete. |
| OS-SCHED-003 | Preemptive context switch hook | Platform | `arch/*/context.spl` | I/P | P/V | P | P | P | P | x86_32 routes through runtime hooks; live switching not proven. |
| OS-SCHED-004 | FPU save/restore hook | Platform | `arch/*/context.spl` | I/P | P/V | P | P | P | P | x86_32 no-op and hook paths exist; live FPU not proven. |
| OS-SCHED-005 | Timer-driven reschedule | Shared + platform timer | scheduler + timer interrupt | I/P | N/B | P | P | P | P | Needs live interrupt/timer on x86_32. |
| OS-STOR-001 | FAT32 image creation metadata | Shared build tooling | `make_os_disk.shs`, qemu runner | I/P | P | I/P | I/P | I/P | I/P | x86_32 has disk image output metadata but no acceptance lane. |
| OS-STOR-002 | NVMe block-device lane | x86_64-specific device path today | x86_64 QEMU scenarios | I/V | N | NA | NA | NA | NA | x86_32 needs either NVMe-capable lane or deliberate alternative. |
| OS-STOR-003 | VirtIO block-device lane | Shared concept, platform QEMU args | ARM/RISC-V scenarios | NA | N | I/P | I/P | I/V | I/P | RISC-V VirtIO/FAT32 SMF scenarios are registered and rv64 has local verified notes; x86_32 could reuse this if wired. |
| OS-STOR-004 | VFS executable byte resolution | Shared | `loader/executable_source.spl` | I/V | I/V | I/P | I/P | I/V | I/P | rv64 SMF/fs markers include image read, discovery, and ELF load; x86_32 resolved bytes are accepted by loader but live VFS source is not proven. |
| OS-UI-001 | Text shell launch | Shared app + platform boot | shell app, spawn | I/V | N/B | P | P | P | P | x86_32 shell smoke remains open. |
| OS-UI-002 | Desktop compositor boot | x86_64 first lane | desktop entries, WM | I/V | N | NA/P | NA/P | NA/P | NA/P | Current full desktop acceptance is x86_64-centered. |
| OS-UI-003 | Browser/app probe | Shared app, platform wrappers | app entries | I/V | P/B | P | P | P | P | x86_32 browser probe entry exists but live build is blocked. |
| OS-DRV-001 | PCI device enumeration | Platform + shared drivers | x86_64 PCI lanes | I/P | N | NA | NA | NA | NA | x86_32 would need PCI init proof before NVMe/GUI parity. |
| OS-DRV-002 | Framebuffer/graphics driver | Platform | BGA/VirtIO GPU lanes | I/V | N | P | P | P | P | x86_32 no graphics acceptance lane. |
| OS-DRV-003 | Network device scenario | Platform QEMU + driver | x86_64 scenarios | I/P | N | N | N | N | N | Not part of x86_32 MVP parity unless promoted. |
| OS-REBOOT-001 | Reboot syscall dispatch | Shared syscall + platform reset | `syscall id=16` | I/V | P | P | P | P | P | Shared handler now routes through HAL reset facade and has hosted regression coverage; non-x86 live QEMU reset proof still missing. |
| OS-REBOOT-002 | Platform reset primitive | Platform | HAL reset facade + CPU/SBI primitive | I/V | I/P | NA/P | NA/P | I/P | I/P | Syscall no longer imports x86_64 directly; x86_64 is verified, x86_32 uses CF9 reset, RISC-V uses SBI SRST, ARM awaits PSCI/platform firmware reset. |
| OS-TEST-001 | Hosted unit tests for pure contracts | Shared | `test/unit/os/kernel` | I/V | I/V | I/V | I/V | I/V | I/V | Covers many pieces but does not replace live QEMU. |
| OS-TEST-002 | Gated live QEMU test | Platform | `test/system/*live*` | I/V | P/B | P | P | P | P | x86_32 gated test reports toolchain block, not successful boot. |
| OS-TEST-003 | Full OS acceptance matrix | Cross-platform | QEMU scenarios + serial markers | I/V | N | P | P | P | P | x86_64 is the only full lane in this matrix. |

## Platform Evidence Index

| Platform | Evidence Files | What They Prove | Remaining Proof Gap |
|----------|----------------|-----------------|---------------------|
| x86_64 | `test/system/os/boot_smoke_spec.spl`, `test/system/simpleos_desktop_disk_boot_spec.spl`, `test/system/simpleos_reboot_live_spec.spl`, `test/unit/os/kernel/ipc/syscall_reboot_spec.spl`, `examples/simple_os/arch/x86_64/*` | Baseline boot, desktop, disk, syscall, reboot, app lanes, and reset-facade dispatch exist. | Keep as regression baseline while other platforms catch up. |
| x86_32 | `test/system/os/boot_smoke_spec.spl`, `test/system/simpleos_x86_32_boot_probe_live_spec.spl`, `test/unit/os/kernel/arch/x86_32_*_spec.spl`, `examples/simple_os/arch/x86_32/*` | Target metadata, pure context, int 0x80 register model, hosted trap dispatch, ELF/process-image handoff. | True i386 live boot, live int 0x80 entry, storage, shell, and process diagnostics. |
| arm64 | `examples/simple_os/arch/arm64/fs_exec_entry.spl`, `src/os/kernel/arch/arm64/*`, `test/qemu/os/boot/arm64_boot_qemu_spec.spl`, `test/os/kernel/arch/hal_arm64_phase_a_spec.spl` | ARM64 boot/HAL source and fs-exec entry exist; QEMU boot and HAL tests are present. | First-class acceptance markers for SVC, EL0 handoff, SMF bytes to process image, shell. |
| arm32 | `examples/simple_os/arch/arm32/fs_exec_entry.spl`, `examples/simple_os/arch/arm32/os_entry.spl`, `src/os/kernel/arch/arm32/*`, `test/qemu/os/boot/arm32_boot_qemu_spec.spl` | ARM32 boot entry, fs-exec entry, HAL source, and QEMU boot spec exist. | Clean current live proof, SVC model, user-mode handoff, SMF process image, shell. |
| riscv64 | `examples/simple_os/arch/riscv64/smoke_entry.spl`, `examples/simple_os/arch/riscv64/shared_service_smoke_entry.spl`, `doc/06_spec/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl`, `test/unit/os/kernel/arch/riscv64_trap_model_spec.spl`, `test/qemu/os/usermode/rv64_user_exec_qemu_spec.spl` | RV64 boot, SMF/fs discovery, ELF load markers, trap model, and user-mode specs exist. | Promote live syscall/process/storage/shell markers into the same parity gate shape as x86_64. |
| riscv32 | `examples/simple_os/arch/riscv32/smoke_entry.spl`, `src/os/kernel/arch/riscv32/*`, `test/qemu/os/boot/riscv32_boot_qemu_spec.spl`, `doc/06_spec/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl` | RV32 boot target, HAL source, QEMU boot spec, and registered SMF/fs scenario exist. | Explicit RV32 ecall model, user-mode handoff, ELF32 SMF process proof, shell. |

## Revisited Non-Shared Rows

The rows below split non-shared or platform-heavy rows into smaller features.
Use these rows for implementation tasks so shared logic is not hidden inside
one platform-specific milestone.

| Parent | Smaller Feature | Shared Piece | Platform Piece | x86_64 Next | x86_32 Next | arm64 Next | arm32 Next | riscv64 Next | riscv32 Next |
|--------|-----------------|--------------|----------------|-------------|-------------|------------|------------|--------------|--------------|
| OS-BOOT-005 | Native freestanding kernel build | native-build command model | target backend, C/asm stubs | Keep as release baseline. | Enable i686 backend or file exact backend issue. | Keep arm64 fs-exec boot binary green. | Prove armv7 build from clean workspace. | Keep rv64 SMF/fs lane green. | Prove rv32 build from clean workspace. |
| OS-BOOT-005 | Live serial boot marker | QEMU timeout/capture | machine, CPU, firmware, serial args | Maintain desktop and kernel smoke markers. | Turn gated i386 probe into true serial assertion. | Add/refresh arm64 live boot marker in fs-exec lane. | Add/refresh arm32 live boot marker in fs-exec lane. | Add/refresh rv64 serial marker. | Add/refresh rv32 serial marker. |
| OS-BOOT-006 | Deterministic QEMU exit | shared QEMU result classification | debug-exit, semihosting, SBI, or poweroff path | Keep `isa-debug-exit` lane. | Add i386 debug-exit guest write proof. | Use semihosting or explicit shutdown marker. | Use semihosting or explicit shutdown marker. | Use SBI/poweroff or serial end marker. | Use SBI/poweroff or serial end marker. |
| OS-BOOT-007 | Disk/firmware boot | release image selection | OVMF, BIOS, virt, machine firmware | Keep OVMF/disk desktop lane. | Decide BIOS multiboot disk lane vs direct `-kernel` only. | Keep virt machine media path. | Keep virt/vexpress media path. | Keep virt machine media path. | Keep virt machine media path. |
| OS-HAL-004 | Trap table descriptor model | descriptor data structures | IDT/vector table/trap vector encoding | Keep x86_64 IDT tests. | Add int 0x80 DPL=3 gate tests. | Add vector table descriptor contract. | Add exception vector contract. | Add trap-vector contract. | Add trap-vector contract. |
| OS-HAL-004 | Trap table install in boot | shared interrupt init ordering | `lidt`, VBAR, `stvec`, controller init | Keep APIC/IDT ordering covered. | Wire x86_32 IDT init into boot before user handoff. | Verify VBAR install before SVC/user handoff. | Verify VBAR/vector install. | Verify `stvec` install. | Verify `stvec` install. |
| OS-SYSCALL-003 | Platform syscall register marshal | `SyscallArgs`/`SyscallResult` | per-ISA register ABI | Maintain syscall/sysret model. | Complete int 0x80 live frame. | Define SVC register contract. | Define SVC register contract. | Define ecall register contract. | Define ecall register contract. |
| OS-SYSCALL-004 | Hosted syscall bridge | shared syscall handler | per-arch frame adapter | Keep x86_64 bridge tests. | Expand getpid/brk/exit/spawn coverage. | Add hosted SVC bridge tests. | Add hosted SVC bridge tests. | Add hosted ecall bridge tests. | Add hosted ecall bridge tests. |
| OS-SYSCALL-005 | Live syscall entry | syscall handler dispatch | assembly exception entry/return | Keep live desktop syscall smoke. | Implement save/dispatch/iret for int 0x80. | Prove SVC enters shared handler. | Prove SVC enters shared handler. | Prove ecall enters shared handler. | Prove ecall enters shared handler. |
| OS-SCHED-003 | Initial user frame | shared scheduler context | selectors/status registers/stack ABI | Keep x86_64 user frame proof. | Live i386 user-mode handoff. | Live EL0 handoff proof. | Live user-mode handoff proof. | Live U-mode handoff proof. | Live U-mode handoff proof. |
| OS-SCHED-003 | Context switch primitive | scheduler decision | register save/restore asm | Keep x86_64 switch path covered. | Replace hosted C shim with real switch or document MVP limit. | Verify context switch hook is not stubbed. | Verify context switch hook is not stubbed. | Verify context switch hook is not stubbed. | Verify context switch hook is not stubbed. |
| OS-SCHED-005 | Timer programming | scheduler tick model | PIT/APIC/arch timer/CLINT | Maintain APIC timer smoke. | Add PIT register contract and live tick marker. | Add arch timer tick marker. | Add timer tick marker. | Add CLINT/timer marker. | Add CLINT/timer marker. |
| OS-SCHED-005 | Interrupt acknowledgement | controller abstraction | PIC/APIC/GIC/PLIC ack | Keep APIC EOI proof. | Add PIC EOI no-storm proof. | Add GIC ack proof. | Add interrupt controller ack proof. | Add PLIC/SBI ack proof if applicable. | Add PLIC/SBI ack proof if applicable. |
| OS-EXEC-007 | Resolve argv0 bytes | executable source | platform media availability | Keep VFS/FAT32 path. | Add compile-time x86 lane when backend works. | Prove SMF path bytes in live lane. | Prove SMF path bytes in live lane. | Prove SMF path bytes in live lane. | Prove SMF path bytes in live lane. |
| OS-EXEC-007 | Map new image segments | segment mapper | active page tables | Keep x86_64 live mapping. | Prove x86_32 page table activation. | Prove arm64 user mappings before handoff. | Prove arm32 user mappings. | Prove rv64 user mappings. | Prove rv32 user mappings. |
| OS-EXEC-007 | Replace current task context | scheduler exec | per-arch context frame | Keep exec replacement tests. | Add x86_32 exec replacement test and live smoke. | Add arm64 exec replacement live smoke. | Add arm32 exec replacement live smoke. | Add rv64 exec replacement live smoke. | Add rv32 exec replacement live smoke. |
| OS-EXEC-009 | Choose storage bus | VFS/FAT32 abstraction | NVMe, VirtIO-blk, or semihosting | NVMe/FAT32 remains baseline. | Choose NVMe vs VirtIO-blk for i386. | VirtIO-blk lane. | VirtIO-blk lane. | VirtIO-blk lane. | VirtIO-blk lane. |
| OS-EXEC-009 | Attach disk in QEMU | media path helper | device args per machine | Keep release-first image selection. | Add x86_32 scenario and command test. | Keep arm64 scenario command test. | Keep arm32 scenario command test. | Keep rv64 scenario command test. | Keep rv32 scenario command test. |
| OS-EXEC-009 | Read executable bytes | executable source | boot device init | Keep `/sys/apps` bytes proof. | Verify `/sys/apps/hello_world.smf` bytes reach loader. | Verify app SMF bytes reach loader. | Verify app SMF bytes reach loader. | Verify app SMF bytes reach loader. | Verify app SMF bytes reach loader. |
| OS-STOR-002 | PCI enumeration | device registry | PCI config mechanism | Keep x86_64 PCI lab. | Needed only if using NVMe/PCI VirtIO. | NA unless PCI device chosen. | NA unless PCI device chosen. | NA unless PCI device chosen. | NA unless PCI device chosen. |
| OS-STOR-003 | VirtIO block read | block interface | MMIO or PCI transport | Optional; NVMe baseline exists. | Needed if choosing VirtIO-blk. | Keep VirtIO-blk live proof. | Keep VirtIO-blk live proof. | Keep VirtIO-blk live proof. | Keep VirtIO-blk live proof. |
| OS-REBOOT-001 | Reboot permission check | capability gate | none | Add/keep allowed and denied tests. | Add trap-bridge denied/allowed test without reset. | Add shared permission tests. | Add shared permission tests. | Add shared permission tests. | Add shared permission tests. |
| OS-REBOOT-002 | Reset primitive abstraction | `system_reset()` facade | x86 port IO, PSCI, SBI, board reset | Move x86_64 import behind facade. | Implement i386 reset backend. | Implement PSCI/semihost reset backend. | Implement board reset backend. | Implement SBI reset backend. | Implement SBI reset backend. |
| OS-UI-001 | Shell binary image | shared app packaging | per-arch executable bytes | Keep shell app packaged. | Create i386 shell SMF after backend works. | Package arm64 shell SMF. | Package arm32 shell SMF. | Package rv64 shell SMF. | Package rv32 shell SMF. |
| OS-UI-001 | Shell spawn smoke | spawn/syscall/shell command loop | live trap and storage | Keep x86_64 shell smoke. | Add serial marker for shell task and one command. | Add shell task marker. | Add shell task marker. | Add shell task marker. | Add shell task marker. |
| OS-UI-003 | Browser/app probe build | shared app code | native build target | Keep x86_64 browser probe. | Unblock i686 build; keep as probe first. | Build app probe if GUI lane is promoted. | Build app probe if GUI lane is promoted. | Build app probe if GUI lane is promoted. | Build app probe if GUI lane is promoted. |
| OS-DRV-002 | Text framebuffer fallback | UI drawing API | VGA/BGA/virtio/fb device | Keep BGA/desktop baseline. | Consider VGA text-mode smoke before graphics. | Use framebuffer/semihost text marker first. | Use framebuffer/semihost text marker first. | Use serial/text marker first. | Use serial/text marker first. |
| OS-TEST-003 | Parity gate definition | acceptance checklist | per-platform live spec | Baseline full OS lane. | Must pass boot, trap, process, storage, shell live. | Must pass boot, trap, process, storage, shell live. | Must pass boot, trap, process, storage, shell live. | Must pass boot, trap, process, storage, shell live. | Must pass boot, trap, process, storage, shell live. |

## Immediate Platform Work Orders

### x86_64

1. Keep x86_64 as the baseline full OS lane while other platforms catch up.
2. Maintain the shared HAL reset facade as the syscall reset boundary.
3. Preserve desktop, shell, NVMe/FAT32, and process diagnostics live smoke coverage as regression gates.

### x86_32

1. Add pure x86_32 IDT gate descriptor tests for `int 0x80`.
2. Implement the x86_32 assembly/C trap-entry bridge against `X86Context`.
3. Add a live i386 boot probe that reaches serial output and exits via debug-exit.
4. Add a live syscall probe for `getpid`, `brk(0)`, and `exit`.
5. Add x86_32 disk scenario command tests before implementing storage live boot.
6. Add live spawn/exec of a tiny i386 ELF or SMF app.
7. Add shell/process diagnostics smoke only after live syscall and storage are stable.

### arm64

1. Make the arm64 fs-exec lane a first-class acceptance lane with boot, storage, spawn, and exit markers.
2. Add hosted SVC frame-marshalling tests that call the shared syscall handler.
3. Prove EL0 user handoff, stack pointer, and return path in QEMU.
4. Verify SMF bytes are read from the FAT32/VirtIO media and become a `UserProcessImage`.
5. Add shell/process diagnostics smoke after SVC and user mappings are stable.

### arm32

1. Prove clean armv7 freestanding build and QEMU launch from the current workspace.
2. Add SVC register-contract tests for the 32-bit ABI.
3. Prove user-mode handoff and stack alignment in live QEMU.
4. Keep FAT32/VirtIO SMF media path aligned with arm64 but with arm32 ELF validation.
5. Add shell/process diagnostics smoke after syscall and storage proof.

### riscv64

1. Keep the RISC-V SMF/fs launch lane green and make serial markers explicit for boot, VFS read, spawn, and exit.
2. Add hosted ecall frame-marshalling tests for the shared syscall handler.
3. Prove U-mode handoff and trap return with `getpid`, `brk(0)`, and `exit`.
4. Verify FAT32/VirtIO SMF app bytes reach `build_user_process_image`.
5. Add shell/process diagnostics smoke after live syscall and storage proof.

### riscv32

1. Prove clean rv32 freestanding build and QEMU launch from the current workspace.
2. Add hosted ecall frame-marshalling tests for RV32 register width and return value truncation.
3. Prove U-mode handoff and trap return with `getpid`, `brk(0)`, and `exit`.
4. Keep FAT32/VirtIO SMF media path aligned with rv64 but with ELF32 validation.
5. Add shell/process diagnostics smoke after live syscall and storage proof.
