# Feature: multiarch-qemu-systest

## Raw Request
run the arm64 fs-exec test → impl the plan for the remaining lanes (riscv32, arm32,
x86_64) with tests and parallel agents (Sonnet impl, Opus review) → add a hosted
aarch64 (mac) lane → research and remove duplication → run the final full sweep and
update doc/guide/spipe/skill and push.

## Task Type
feature + verification

## Refined Goal
Bring every SimpleOS fs-exec systest lane to an honest, verified state: 6 bare-metal
QEMU lanes (riscv32/riscv64/arm32/arm64/x86_32/x86_64) booting green from committed
source, plus a 7th hosted aarch64-apple-darwin lane (native macOS process, honest
missing-media RED on Linux). Remove cross-arch duplication safely (verify-or-revert),
and document the whole thing (plan, guide, skill, this spipe).

## Acceptance Criteria
- AC-1: arm32, riscv32, x86_64 lanes GREEN — all contract markers on the wire,
  binary-safe verified, green-making source on origin. ✅ DONE.
- AC-2: 7th hosted aarch64-darwin lane wired into contract + build matrix; spec
  compiles and returns honest `missing-media` RED on Linux (GREEN only on Apple
  Silicon). ✅ DONE.
- AC-3: Duplication analyzed + removed (−~830 L) into `arch/common/*`, each
  extraction verify-or-revert (build-verify where buildable, static-equivalence
  where not). ✅ DONE.
- AC-4: Final full fresh boot-sweep run + per-lane verdict recorded; reproducibility
  caveats and any regression filed as bugs. ✅ DONE (riscv64 RED — see Status).
- AC-5: doc + guide + skill + spipe updated and pushed to origin. ⏳ this commit.

## Status (2026-06-14)
| Lane | State |
|------|-------|
| riscv32 | GREEN (LLVM driver — cranelift blocks rv32) |
| arm64 | GREEN (genuine EL0) |
| arm32 | GREEN |
| x86_32 | GREEN |
| x86_64 | GREEN (NVMe + FAT32, O1 ratified) |
| riscv64 | **RED** — both backends boot OpenSBI then die silent; good Jun-8 ELF lost. Bug `riscv64_cranelift_smf_fs_boot_regression_2026-06-14` |
| aarch64-darwin | hosted — RED on Linux (missing-media), GREEN on Apple Silicon |

Net: **5/6 QEMU lanes GREEN + darwin hosted**; riscv64 regressed (artifact lost,
not source-reproducible this session).

## Next Steps (open)
1. **riscv64 restore** — bisect/debug why the rebuilt kernel dies right after the
   OpenSBI handoff (both LLVM+cranelift; 86 KB good → 164–171 KB bad). Highest
   priority open item.
2. **arm64 rebuild env** — fix x86 kernel modules being pulled into arm64 source
   scope so arm64 is source-reproducible (currently green from committed ELF).
3. **riscv32 LLVM-driver requirement** — wire the LLVM driver into the standard
   build tooling so rv32 isn't a manual step.
4. Dedup tier 4 (contract→platform_targets table, ~270 L) is BLOCKED by the
   interpreter struct-array-literal hang — revisit when that's fixed.

## Key References
- Plan: `doc/03_plan/os/multiarch_qemu_systest/remaining_lanes_plan.md`
- Guide: `doc/07_guide/os/multiarch_qemu_systest_guide.md`
- Skill: `.claude/skills/multiarch_systest.md`
- Dedup analysis: `doc/05_design/os/multiarch_qemu_systest/duplication_analysis.md`
- Contract: `src/os/qemu_systest_contract.spl`
