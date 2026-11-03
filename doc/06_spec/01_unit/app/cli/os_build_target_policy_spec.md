# OS build target policy

**AUTHORED_UNRUN.** No admitted Simple runner was available. This manual is authored; docgen and actual TDD RED/GREEN were not run. No QEMU process, native build or bootstrap was started.

Executable: `test/01_unit/app/cli/os_build_target_policy_spec.spl`.
Requirement: REQ-CLI-OS-BUILD-001.
Canonical bug: `app_modules_referenced_by_specs_exist_nowhere_2026-08-04`.

The missing-inline-symbol portion has already been repaired. Its canonical report separately identifies the live `os.cli.handle_os_build` regression: it selects filesystem-backed QEMU acceptance targets instead of kernel smoke targets. The restored inline CLI build wrapper already uses the smoke policy. This change makes the actual OS CLI build route agree.

The production target-selection helper is called by `handle_os_build`; the two scenarios call that same helper and assert exact catalog contracts:

| Architecture | Kernel entry | Output | Extra QEMU devices |
|---|---|---|---|
| ARM64 | src/os/kernel/arch/arm64/boot.spl | build/os/simpleos_aarch64.elf | None |
| RISC-V64 | src/os/kernel/arch/riscv64/boot.spl | build/os/simpleos_riscv64.elf | None |

Each scenario selects its production build target, then checks the kernel entry, output and empty extra-device list. This is selection behavior, not proof of a successful kernel compile or guest boot. Named scenarios and run/test acceptance-target selection retain their existing behavior. The broader canonical record stays open pending qualified verification.
