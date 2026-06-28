# QEMU System Tests Multi-Arch Plan — 2026-06-13

Goal: SSpec system tests booting real QEMU per arch (x86_64, x86_32, arm32,
arm64/aarch64, riscv64, riscv32); fix the P1 platform-catalog crash blocking
`bin/simple os`; perf + stability fixes on compiler and OS; minimize QEMU
storage overhead; update doc/guide/spipe skill. Parallel agents, model-rated
tasks, opus review after.

## Known facts (this session)
- Live riscv64 QEMU boot WORKS via direct qemu-system invocation with the lane
  contract args (serial: SIMPLEOS_RISCV_SMF_FS_PASS / TEST PASSED).
- `bin/simple os <anything>` is broken by P1
  doc/08_tracking/bug/interp_simpleos_lane_contract_crash_2026-06-13.md:
  `simpleos_platform_qemu_smoke_lane` → 'qemu_smoke_lane' on Option (seed) /
  SIGSEGV (stage4). Pre-existing, blocks lane runner + kernel rebuilds.
- FAT32 images: 4 MB each, 40 MB total — already lean. Remaining storage:
  stale QMP/serial logs, duplicate probe images, FreeBSD VM overlays.
- arm64 fs-exec kernel ELF missing on host; riscv64/riscv32/arm32/x86 ELFs +
  all FAT32 images present.

## Tracks (disjoint scopes)

| Track | Scope (exclusive) | Lead | Spipe feature |
|-------|-------------------|------|---------------|
| A p1-catalog-fix | `src/os/port/_SimpleosMultiplatformBuild/platform_target_accessors.spl` (+part1 struct if needed), repro spec | sonnet | `p1_catalog_option_fix` |
| B qemu-systest | `test/03_system/os/qemu/**` (new), `src/os/qemu_systest_contract.spl` (new helper) | sonnet | `qemu_systest_multiarch` |
| C storage+docs | `doc/07_guide/platform/simpleos/**`, `.claude/skills/spipe.md` (system-test section), `scripts/check/qemu-storage-*.shs` (new) | haiku→sonnet review | `qemu_storage_docs` |
| D compiler-fix | `src/compiler/**` decorator/skip lowering bug + JIT fallback noise | sonnet | `compiler_jit_lowering_fix` |

## Task breakdown (model-rated)

### A — P1 catalog Option fix (unblocks bin/simple os)
- A1 (sonnet): root-cause in .spl: `simpleos_platform_target_by_name -> T?`
  returning a large nested struct miscompiles in interpreter (Option unwrap
  yields Option / SIGSEGV). Restructure .spl-side to avoid Option<large-struct>:
  return target INDEX (i64, -1 = missing); accessors fetch
  `simpleos_platform_targets()[idx]` locally. Keep public signatures.
  Rust seed NOT to be touched; bug doc stays open for the interpreter fix.
- A2 (haiku): verify `bin/simple os targets` + seed equivalent both work;
  run qemu_runner unit specs; protection-acceptance spec un-broken?
- A3 (sonnet): rebuild missing arm64 fs-exec kernel (`bin/simple os build
  --arch=arm64 --scenario=arm64-virtio-fat32-smf`) once unblocked.

### B — SSpec QEMU system tests per arch
- B1 (sonnet): new helper `src/os/qemu_systest_contract.spl`: build QEMU argv
  from (arch, kernel, image) mirroring lane contracts; run with timeout;
  capture serial to build/os/systest/<arch>.serial.log; classify result
  (pass markers / missing-media / boot-fail) — fail-closed, media-missing is a
  distinct diagnosed failure not a skip.
- B2 (sonnet): specs `test/03_system/os/qemu/sys_qemu_<arch>_fs_exec_spec.spl`
  for riscv64, riscv32, arm32, arm64, x86_64, x86_32: boot real QEMU, assert
  required markers + `fs_exec_serial_has_fallback == false` on healthy boot.
  Follow sspec environmental-test guidance (doc/07_guide/infra/sspec_scenario_manual.md).
- B3 (haiku): wire into test discovery; run riscv64 + any other green lanes
  live; record evidence per arch in the state file.

### C — Storage minimization + doc/guide/spipe/skill updates
- C1 (haiku): audit `du` of build/os, build/freebsd, stale *qmp*.log,
  *.serial.log, duplicate probe imgs; write `scripts/check/qemu-storage-audit.shs`
  printing reclaimable bytes; document retention policy (keep latest serial per
  lane, delete QMP logs >7 days).
- C2 (haiku): guide `doc/07_guide/platform/simpleos/qemu_system_tests.md`:
  how to run per-arch system tests, direct-boot fallback while P1 open,
  storage policy, marker contracts.
- C3 (sonnet): spipe skill: add system-test-over-qemu section to
  `.claude/skills/spipe.md` (or lib/spipe_phases.md) referencing the new specs
  and helper; keep ≤30 lines per diagram rule.

### D — Compiler fix (perf/stability)
- D1 (haiku): reproduce + inventory the JIT fallback spam seen on every spec
  run: "HIR lowering error: Unknown variable: decorator while lowering skip"
  and "Unknown type: Lexer" — find the lowering site and what triggers it.
- D2 (sonnet): fix root cause in pure Simple (likely std.spec `skip`
  decorator symbol not registered in HIR lowering) so spec files JIT instead
  of falling back to interpreter — measurable spec-runtime perf win; record
  before/after timing on a fixed spec set.
- D3 (haiku): re-run codegen + bridge + http specs to confirm no regression.

## Review
Opus review per track after implement-done (same protocol as previous wave:
verify no hollow asserts, no cover-ups, claims vs reality, scope).

## Process rules
- Same as prior wave: commit per sub-batch immediately; interpreter-mode spec
  verification; SIMPLE_BOOTSTRAP_DRIVER for stage4; no skip()/weakened asserts;
  media-missing must fail with diagnosis, never silently pass.
