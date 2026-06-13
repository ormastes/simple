# Feature: fs_exec_multiarch

## Raw Request
with spipe dev skill, harden simple os file-system-based file execution on x86, riscv, aarch64; small model-rated tasks, parallel agents, higher-model review after.

## Task Type
code-quality

## Refined Goal
FS-loaded execution proof contracts are fail-closed and arch-uniform (x86_64, riscv32/64, arm64), and the kernel loader rejects malformed images with bounds-checked parsing.

## Acceptance Criteria
- AC-1: A written gap map exists of fs-exec proof/marker coverage per arch (x86_64, riscv64, riscv32, arm64) derived from qemu_runner*.spl and contracts.
- AC-2: Resident-manifest fallback is rejected as completion evidence on riscv and arm lanes with the same fail-closed semantics as x86_64, via shared contract logic (no per-arch copy drift); specs prove rejection per arch.
- AC-3: Kernel loader SMF/image load path bounds-checks sizes/offsets and rejects truncated images with an error; unit specs in test/01_unit/os/kernel/loader/.
- AC-4: All touched contract specs pass in interpreter mode; no QEMU live lane is newly required.

## Scope Exclusions
No changes to src/os/apps/** or src/lib/**. No new QEMU scenarios; contract/loader level only. desktop_qemu_contract.spl marker strings must not diverge.

## Phase
dev-done

## Log
- dev: Created state file with 4 acceptance criteria (type: code-quality)
