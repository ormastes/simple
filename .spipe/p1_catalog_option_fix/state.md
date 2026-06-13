# Feature: p1_catalog_option_fix

## Raw Request
perf and others fix on both compiler and os (goal 2026-06-13): fix the P1 platform-catalog Option crash blocking bin/simple os.

## Task Type
bug

## Refined Goal
`bin/simple os targets` (and every catalog-lane accessor) runs without crash in both seed-interpreter and stage4 by restructuring the .spl catalog accessors to avoid returning Option<large-struct> across calls.

## Acceptance Criteria
- AC-1: `bin/simple os targets` prints all architectures and exits 0 (stage4 binary), and the seed driver does the same.
- AC-2: The bug-doc repro (simpleos_platform_qemu_smoke_lane("riscv64")) returns a lane contract in interpreter mode without 'on Option' error or SIGSEGV; a regression spec encodes it.
- AC-3: Public function signatures of simpleos_platform_* accessors unchanged (callers in qemu_runner_part1-5 unmodified and still check-clean).
- AC-4: test/01_unit/os/qemu_runner_protection_acceptance_spec.spl passes (was 3/3 failing on this bug); qemu_runner_fs_exec_fallback_acceptance_spec still 10/10.
- AC-5: Rust seed untouched; bug doc updated with the .spl-side workaround and stays open for the interpreter root cause.

## Scope Exclusions
No Rust seed changes. No qemu_runner_part*.spl changes. No new scenarios.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug)
