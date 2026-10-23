# Bootstrap in the Cloud — Plan and Progress

**Date:** 2026-10-22 · **Branch of record:** `release/1.0.0` (with `release_phase3` kept equal to it)
**Goal:** every lane climbs Rust seed → phase 1 → phase 2 → phase 3 → phase 4 on hosted CI, each RC moves the default compiler forward, and the user can drive any lane by hand.
**Parent plan:** `free_github_actions_ci_plan_2026-10-22.md` (the full 20-lane design; this file covers the bootstrap slice that is in flight).

## 1. Lanes

| # | Lane | Where it runs | How a phase is built |
|---|---|---|---|
| 1 | linux-x86_64 | `ubuntu-24.04` | native |
| 2 | linux-riscv64 | `ubuntu-24.04` | cross-built by lane 1's previous phase; sanity under qemu-user (or ria-jit) |
| 3 | darwin-arm64 | `macos-15` | native (3 threads, 7 GB runner) |
| 4 | darwin-x86_64 | `macos-15-intel` | native |
| 5 | windows-x86_64 | `windows-2025` | native; default toolchain moving to MinGW UCRT (CLANG64 + LLD), MSVC kept selectable |
| 6 | freebsd-x86_64 | `ubuntu-24.04` + `vmactions/freebsd-vm` | native in the VM |
| 7 | freebsd-riscv64 | local QEMU guest (no hosted runner) | stage builds in the guest with cranelift |

## 2. Machinery (landed)

| Piece | File | Role |
|---|---|---|
| Phase ladder | `.github/workflows/phase-ladder.yml`, `phase-ladder-rung.yml` | Four rungs; each lane climbs one phase per rung, capped at 4; then publishes the reached phases as the next `rc-<base>-rc.N`. Push to `release/**`/`release_phase3`, nightly 04:17 KST, manual with `lanes=` / `publish=` |
| One rung | `scripts/bootstrap/phase-ladder-step.shs` | Picks the lane's highest handoff, builds the next phase, requires hello build + run |
| Compiler selection | `config/bootstrap.sdn` (`compiler: auto`), `scripts/bootstrap/resolve-bootstrap-compiler.shs` | Local stage 4→1, then newest RC, then seed; every candidate must build and run hello |
| Next phase | `scripts/bootstrap/build-next-phase-ci.shs` | Builds stage N+1 with the resolved compiler |
| Cross CPU | `scripts/bootstrap/cross-arch-bootstrap.shs` | linux/freebsd × riscv64/aarch64; env-tunable threads, timeouts, emulator |
| RC drop | `release.yml` `rc-drop` | Numbered prereleases from whatever built |
| Component builds | `.github/workflows/component-build.yml`, `config/ci/components.sdn`, `scripts/ci/plan-components.shs` | Kernels, plugins, providers, SIMD (AVX-512, aarch64 cross) rebuilt only when their paths change, with a proven compiler; per-branch cache keyed by compiler digest |

Manual runs (the workflows reached `main` with #4144):

```sh
gh workflow run phase-ladder.yml --ref release/1.0.0
gh workflow run phase-ladder.yml --ref release/1.0.0 -f lanes=linux-x86_64,windows-x86_64 -f publish=false
gh workflow run component-build.yml --ref release/1.0.0 -f components=simd-x86_64-avx512
```

## 3. Progress (2026-10-23, 15:41 UTC; ladder run 39962905298)

| Lane | Phase 1 | Phase 2 | Phase 3–4 | State |
|---|---|---|---|---|
| linux-x86_64 | ⏳ rung 1 (seed build) | ❌ naming probe | — | #4225 moved stage 2 past p2_add/scv_prime/mir_retention; `stage2_module_path_naming` SEGVs (walk_hir_type, representation-manifest pass), open bug |
| linux-riscv64 | ✅ cross-built | — | — | climbs one rung behind linux-x86_64 |
| darwin-arm64 | ⏳ rung 1 (seed build) | ❌ link | — | `_simple_note_user_threads_started` weak ref fails on ld64; fix proposed on #4225, not pushed |
| darwin-x86_64 | ❌ hello SEGV | — | — | phase 1 builds but SEGVs (exit 139) compiling the hello sanity at native_compile; seed's LLVM also missing on Intel macOS |
| windows-x86_64 | ❌ | — | — | rung still on MSVC: clang-cl LNK1120 and a `simple-term-io` build-script failure; MinGW rung setup is unlanded |
| freebsd-x86_64 | ✅ hello passes | — | — | phase 1 built from the seed in the VM; the essentials step then died (`ssh exited with code 2`), handoff lost (upload now runs on failure) |
| freebsd-riscv64 | ✅ hello runs | ⏳ guest | — | local VM down after container restart; needs a runtime rebuild with #4151/#4225 |

### Landed today
- #4142 version line restored to `1.0.0-rc.1`; #4143, #4147 `release_phase3` ⇄ `release/1.0.0` synced (fast-forward, no force push).
- #4137 riscv64 relax-marker tombstone filter + riscv64 sysroot libraries.
- #4139 lane fixes: FreeBSD self-exe via procstat, cranelift seed skips LLVM-C import, cross jobs add target std, macOS lane on LLVM 23, stage-2 binary kept on failure.
- #4145 phase ladder, component builds, the free GitHub Actions CI plan.
- #4146 LLVM check is strict on major 23 only; other 23.x.y warn.
- #4149 (owner) pinned LLVM discovery for clang-cl/lld-link.

### Landed in this round
- #4225 transient promote walks unowned roots that hold scope-owned children (stage-2 publish SEGV); stage 2 now passes p2_add, scv_prime and mir_retention on CI.
- #4234 phase ladder builds phase 1 from the Rust seed when no RC qualifies (every native lane had failed rung 1); records the naming-probe walk_hir_type site.
- #4144 `release/1.0.0` → `main` (owner admin merge, 09:17 UTC).
- #4152 component builds report SKIPPED (with the resolver's reason) until a proven compiler qualifies, instead of failing every `src/` PR.
- #4151 `rt_transient_heap_promote` promotes scope-owned heap roots. Root cause of the stage-2 SEGV on every lane: the Rust twin returned `true` for any registered heap root, so the retained parse `Result<ParserModule>` was freed at scope end and `surface_build` read a dangling module. New regression test fails without the fix; runtime lib failures 19 → 10, none new.

### In review
- #4148 process spawn falls back to POSIX `set -m` job control when neither `setsid` nor `perl` exists (FreeBSD base, the riscv64 guest). Verified on FreeBSD 14.4 riscv64 `/bin/sh`.

## 4. Blockers and decisions

| Item | Owner | Status |
|---|---|---|
| Stage-2 SEGV (`surface_build`) | us | fixed by #4151 (landed); confirm with a rebuilt stage 2 on CI |
| Manual dispatch of new workflows | done | #4144 put the workflows on `main` |
| No proven compiler in any RC yet | us | rc1 publishes phase-1 packages; component builds stay SKIPPED until then |
| Windows default toolchain | decided | MinGW UCRT via MSYS2 CLANG64 (`x86_64-pc-windows-gnullvm`), LLD linker; MSVC kept, CI builds GNU only, releases switch too |
| LLVM pin | decided | major 23 strict, other 23.x.y warn (#4146) |
| freebsd-riscv64 runtime | us | rebuild `libsimple_native_all.a` for riscv64 FreeBSD with #4151, rerun stage 2 in the guest |

## 5. Next steps (in order)
1. Land #4148 (#4152 and #4151 landed; `release/1.0.0` requires up-to-date branches).
2. Run the ladder on `release/1.0.0` (all lanes); expect phase 2 on lanes 1, 3, 4, 5, 6 and linux-riscv64 phase 2 from the cross rung.
3. Publish the reached phases as the next RC; confirm `resolve-bootstrap-compiler.shs` picks it up (component builds turn from SKIPPED to running).
4. Land the Windows MinGW UCRT PR after its Windows CI shows a GNU stage 1 that builds and runs hello.
5. Rebuild the riscv64 FreeBSD runtime with #4151 and continue the guest to phase 4.
6. Repeat ladder runs until every lane reports phase 4; each publish moves the default compiler forward.

## 6. Ground rules kept
- Land via PR only; `release_phase3` is fast-forwarded to the release tip, never force-pushed.
- A missing compiler, an emulator failure or a missing final record is SKIPPED or FAILED, never PASS.
- Phases cap at 4; a phase-4 compiler rebuilding itself stays phase 4.
- Release branch is the branch of record; `main` follows through an owner admin merge.
