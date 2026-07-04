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
  caveats and any regression filed as bugs. ✅ DONE (all 6 QEMU lanes GREEN — see Status).
- AC-5: doc + guide + skill + spipe updated and pushed to origin. ⏳ this commit.

## Status (2026-06-14)
| Lane | State |
|------|-------|
| riscv32 | GREEN (LLVM backend auto-selected for rv32) |
| arm64 | GREEN (genuine EL0) |
| arm32 | GREEN |
| x86_32 | GREEN |
| x86_64 | GREEN (NVMe + FAT32, O1 ratified) |
| riscv64 | **GREEN** — source-reproducible (fixed: accidental boot-dir wrapper pulled the 100 KB networking runtime into the minimal kernel; renamed). Bug `riscv64_cranelift_smf_fs_boot_regression_2026-06-14` closed. Verified: fresh 78 KB build, real OpenSBI boot, 6/6 markers |
| aarch64-darwin | hosted — RED on Linux (missing-media), GREEN on Apple Silicon |

Net: **6/6 QEMU lanes GREEN + darwin hosted**; riscv64 + arm64 now
source-reproducible (fixed 2026-06-14).

## Next Steps (open)
1. ~~riscv64 restore~~ ✅ DONE 2026-06-14 — root cause was an accidental
   `arch/riscv64/boot/freestanding_runtime.c` wrapper `#include`-ing the 100 KB
   networking runtime; the linker boot-dir glob + minimal allowlist compiled it in
   (78→175 KB, displaced reset vector). Renamed → `full_networking_runtime.c`.
   Verified 6/6 markers on a fresh build.
2. ~~arm64 rebuild env~~ ✅ DONE 2026-06-14 — `arch/arm64/boot/glass_render.c` was
   a symlink to the x86_64 157 KB GUI file (boot-dir glob pulled it in). Removed;
   source-reproducible. The same symlink in `arch/riscv64/boot/` was also removed.
3. ~~riscv32 LLVM-driver wiring~~ ✅ DONE 2026-06-14 — the driver now auto-selects
   the LLVM backend for rv32 targets (`compile_commands.rs` + `native_build.rs`);
   explicit `--backend` still wins.
4. ~~linker.rs boot-dir glob footgun~~ ✅ DONE 2026-06-14 (gated, not rewritten).
   The compiler auto-globs every `.c`/`.S` in `arch/<arch>/boot/`, so a stray
   wrapper or cross-arch symlink is silently compiled in — the shared root cause of
   the riscv64 + arm64 bugs. Rather than rewrite the core glob (would break every
   lane — the manifests weren't complete), the existing `native_surface_policy_verify`
   is now a **fail-closed gate**: completed the per-lane boot-source manifests (15
   legit sources), made `find` catch symlinks (was `-type f` only), added
   `scripts/check-simpleos-native-surface.shs`, and wired it into the pre-commit hook
   (runs when boot/runtime/manifest files change). Verified: planted symlink AND
   planted stray `.c` both FAIL; clean tree PASSes. Origin tip `e81a1794602`.
5. ~~Dedup tier 4 (contract→platform_targets table)~~ ✅ CLOSED 2026-06-14 — NOT
   WORTH DOING. Probe showed the interpreter reads `simpleos_platform_targets()`
   fine (no seed fix needed), but the ~270 L "savings" is illusory: the contract's
   qemu-arg lists are per-lane-unique (NVMe / virtio / dual-loader / semihosting)
   and not stored in the struct, and lane markers are `[]` in the table. Delegating
   would just relocate the logic. Decision: keep explicit per-lane contract
   functions. See `duplication_analysis.md` Tier 4.

## Key References
- Plan: `doc/03_plan/os/multiarch_qemu_systest/remaining_lanes_plan.md`
- Guide: `doc/07_guide/os/multiarch_qemu_systest_guide.md`
- Skill: `.claude/skills/multiarch_systest.md`
- Dedup analysis: `doc/05_design/os/multiarch_qemu_systest/duplication_analysis.md`
- Contract: `src/os/qemu_systest_contract.spl`
