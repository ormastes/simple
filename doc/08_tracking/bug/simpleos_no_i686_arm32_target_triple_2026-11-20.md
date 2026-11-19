# SimpleOS has no i686 or arm32 target triple (fail-closed, no userland)

- Status: open
- Severity: P2
- Found: 2026-11-20 (ubuntu-p2 cross lint/test-runner matrix: sos-i686 and sos-arm32 rows cannot run)
- Component: compiler backend target triples (`src/compiler/70.backend/backend`), SimpleOS userland
- Related: `simpleos_userland_lint_test_runner_xc_gaps_2026-11-15.md` (gap 5)

## Observation
SimpleOS user triples exist only for x86_64, aarch64 and riscv64gc (plus a riscv32imac link lane).
`i686-*-simpleos` and `armv7-*-simpleos` are not mapped to any object target and are
rejected on purpose before link, so no lint/test-runner binary can be produced for them.

## Evidence
- `aot_target_normalization.spl:4-19` `backend_aot_simpleos_target_triple` maps only x86_64, aarch64, riscv64/riscv64gc; everything else returns "".
- `aot_target_normalization.spl:21-32` `backend_aot_simpleos_32bit_user_target_error` refuses `{i686,i386,armv7*,riscv32*}-*simpleos*` (`TODO(simpleos_32bit_userland)`); called from `llvm_native_link_orchestrator.spl:208`.
- `llvm_target.spl:198-207` SimpleOS `LlvmTargetTriple` is built only for x86_64, AArch64, Riscv64; the 32-bit case falls to the `case _` comment "rejects every unsupported and 32-bit SimpleOS target".
- `simpleos_native_symbols.spl:106-107` riscv32imac is recognised only as a freestanding kernel-lane target.
- Existing spec `test/01_unit/compiler/backend/simpleos_cranelift_target_normalization_spec.spl` pins `armv7-unknown-simpleos` -> "".
- Kernel arch dirs exist (`src/os/kernel/arch/x86_32`, `arm32`), so the gap is the triple, crt0, libc archive, sysroot, user linker script and link path, not the kernel HAL.

## What is needed
Triple spellings (`i686-unknown-simpleos`, `armv7-unknown-simpleos`) mapped to freestanding object targets,
`LlvmTargetTriple`/`CodegenTarget` cases, crt0 + libc archive + user linker script + sysroot per arch, and a link path
in the orchestrator; then remove the 32-bit refusal and flip the spec below.

## Spec
`test/01_unit/compiler/backend/simpleos_i686_arm32_triple_spec.spl` (`@tag:in-development`, assert-only; expected to fail until implemented).
