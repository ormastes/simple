# BUG: riscv64 smf_fs kernel — cranelift rebuild produces non-booting ELF (pre-existing regression)

- **ID:** riscv64_cranelift_smf_fs_boot_regression_2026-06-14
- **Severity:** P1 (reproducibility — lane green only from a stale artifact)
- **Found:** 2026-06-14, during multiarch dedup verification (riscv dedup agent)
- **Component:** compiler/cranelift backend → riscv64 freestanding kernel codegen
- **Status:** OPEN

## Symptom

Rebuilding `build/os/simpleos_riscv64_smf_fs.elf` from current source produces a
~164–171 KB ELF that boots far enough for **OpenSBI** to load (banner appears) but
the kernel then emits **no markers** (silent death right after the OpenSBI handoff).
The last known-good artifact was the **Jun 8 86 KB** ELF (booted green, all 6
markers: `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `SIMPLEOS_RISCV_SMF_FS_PASS`, `TEST PASSED`).

**UPDATE 2026-06-14 (full-sweep verification):** NOT cranelift-specific — the
**LLVM** backend fails identically (164 KB ELF, OpenSBI banner then silence). And
the good 86 KB artifact was **overwritten** during dedup verification, so the lane
is now RED in a fresh sweep (it was previously green only because the stale Jun 8
artifact was still on disk; riscv64 was never source-reproducible this session).
The ~2× size jump (86 KB → 164–171 KB) on both backends points at a riscv64 kernel
build/codegen change, not a backend bug. riscv32 (same shared `riscv_common.h`,
LLVM backend) builds and boots GREEN — so the fault is riscv64-specific.

## Scope / proof it is PRE-EXISTING (not caused by the dedup)

Confirmed by rebuilding with the **original, unmodified** `arch/riscv64/boot/
baremetal_stubs.c` from git (pre-dedup): the rebuild fails **identically** (171 KB,
no markers). The 2026-06-14 riscv64 boot-stub dedup (`riscv_common.h` extraction)
was separately proven a pure refactor (normalized translation-unit diff = header
guards + one forward declaration, zero function-body changes), so it is NOT the
cause. The regression was introduced in the cranelift backend / riscv64 codegen
some time between Jun 8 and Jun 14.

## Impact

- The riscv64 fs-exec systest lane (`sys_qemu_riscv64_fs_exec_spec.spl`) is GREEN
  only because the stale Jun 8 ELF is still present on disk. It is **not currently
  reproducible from source** with the default backend.
- This is a latent CI hazard: a clean checkout + rebuild would yield a RED riscv64
  lane until this is fixed.

## Repro

```
unset SIMPLE_ALLOW_FREESTANDING_STUBS
env SIMPLE_BOOT_MINIMAL=1 src/compiler_rust/target/debug/simple native-build \
  --source build/os/generated --source src/os --source examples/09_embedded/simple_os \
  --backend cranelift --opt-level=aggressive --log on --entry-closure \
  --entry examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl \
  --target riscv64-unknown-none-elf -o /tmp/rv64_probe.elf \
  --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld
# Boot with riscv64_qemu_args(); observe: no markers on serial.
```

## Next steps (not yet done)

1. Bisect cranelift / riscv64 codegen between the Jun 8 good build and now.
2. Compare the 86 KB (good) vs 171 KB (bad) ELF: section layout, entry, relocations,
   BSS/stack init — the size jump suggests a codegen/layout change (e.g. bad
   inlining, missing GC/strip, or a runtime-init path that now faults early).
3. Cross-check whether riscv32 (which builds GREEN only via the **LLVM** backend —
   cranelift blocks rv32 entirely) shares a root cause in the cranelift rv path.

## Related

- riscv32 builds green only with the LLVM-backed driver (cranelift blocks rv32).
- Multiarch lane status + dedup plan: `doc/03_plan/os/multiarch_qemu_systest/`
  and `doc/05_design/os/multiarch_qemu_systest/duplication_analysis.md`.
