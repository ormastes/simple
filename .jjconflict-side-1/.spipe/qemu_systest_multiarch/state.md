# Feature: qemu_systest_multiarch

## Raw Request
make system test over qemu; make sspec system tests for different set of arch x86, arm, riscv 64,32, aarch64 (goal 2026-06-13).

## Task Type
feature

## Refined Goal
SSpec system tests under test/03_system/os/qemu/ boot real QEMU per architecture (riscv64, riscv32, arm32, arm64, x86_64, x86_32) using the lane-contract args, capture serial, and assert pass markers plus fallback-contract cleanliness, with missing media reported as diagnosed failure (never a silent pass or skip).

## Acceptance Criteria
- AC-1: A helper module (src/os/qemu_systest_contract.spl) builds the per-arch QEMU argv mirroring the catalog lane contracts WITHOUT calling the crashing simpleos_platform_* accessors (P1 still open in interpreter); runs QEMU with timeout; captures serial to build/os/systest/<arch>.serial.log; classifies pass/missing-media/boot-fail.
- AC-2: Six specs sys_qemu_<arch>_fs_exec_spec.spl exist and load clean; each asserts required markers and fs_exec_serial_has_fallback(serial) == false on a healthy boot.
- AC-3: riscv64 spec passes LIVE on this host (kernel+image present). Other arches: live pass where media exists; where kernel ELF is missing the spec fails with classification "missing-media:<path>" (diagnosed failure, not skip) and the state file records which arches are media-blocked.
- AC-4: Specs follow sspec environmental-test guidance (doc/07_guide/infra/sspec_scenario_manual.md) and use expect(x).to_equal(...) only.

## Scope Exclusions
No qemu_runner_part*.spl changes. No src/os/port/** changes (Track A owns the P1 fix). No kernel builds.

## Phase
done

## Per-Arch Live Results (2026-06-13)

| Arch    | Kernel ELF Present | Image Present | Spec Result | Classification |
|---------|--------------------|---------------|-------------|----------------|
| riscv64 | YES                | YES           | LIVE PASS   | pass |
| riscv32 | NO                 | YES           | RED (expected) | missing-media:build/os/simpleos_riscv32_smf_fs.elf |
| arm64   | NO                 | YES           | RED (expected) | missing-media:build/os/simpleos_arm64_fs_exec.elf |
| arm32   | NO                 | YES           | RED (expected) | missing-media:build/os/simpleos_arm32_fs_exec.elf |
| x86_64  | NO                 | YES           | RED (expected) | missing-media:build/os/simpleos_x86_64_fs_exec.elf |
| x86_32  | YES                | YES           | LIVE PASS   | pass |

Unit tests: 13/13 green (classify_serial — pure logic, no QEMU).
Lint: bin/simple build lint src/os/qemu_systest_contract.spl — clean.

## Log
- dev: Created state file with 4 acceptance criteria (type: feature)
- done: Implemented src/os/qemu_systest_contract.spl, 6 system specs, 1 unit spec; riscv64+x86_32 live PASS; riscv32/arm64/arm32/x86_64 correctly diagnosed as missing-media RED
