# Items 5 and 6 release lane qualification (2026-10-10)

Status: IN PROGRESS; release landing blocked.

Branch: `work/targets-release-20261010`, isolated worktree `/tmp/simple-release-targets-worktree-20261010`. Base: `origin/release/1.0` at `2f690c30ba2` when rebased. Current code head before this report: `9050fe878abad386e2bd83b11c771cd95df15083`.

Item 5 narrow repair: `runtime_sqlite_demand.c` now releases the temporary tagged path after the synchronous sealed snapshot call. Matched Clang `-Os -fPIC -ffunction-sections -fdata-sections` C object builds passed. Baseline object: 20,112 bytes; repaired object: 20,200 bytes (+88 bytes, +0.44%). This object comparison is not a hello executable, startup, RSS, or provider closure measurement. The existing selected BS7 synthetic fixture passed earlier on this branch; full Item 5 phases, including production provider matrix, matched release-small cohort and cutover, remain open.

Item 6 candidate repairs on this branch provide stable workspace root identity and a semantic v2 module action key that excludes generation-wide SCV fields. The root identity focused native helper passed earlier. The v2 CAS probe and production edit transition remain unverified on the current source because Stage 2 admission fails. Automatic source-edit admission, exact archive hits, paired time/RSS cohorts, and the full executable acceptance contract remain open.

Bootstrap evidence: the first run was invalidated by an in-flight runtime source edit; the next two stable-source runs built Stage 2 but failed its module-path-naming HIR worker sanity with exit -139, then refused seed fallback. See [the bug](../../08_tracking/bug/item56_stage2_hir_worker_crash_2026-10-10.md). The repository's three-cycle cap ends further bootstrap retries in this session.

Other checks: the C source compiled, `git diff --check` passed before its commit, both `direct-env-runtime-guard` modes passed, and `doc/06_spec` contains zero `*_spec.spl` files. These checks are narrower than a verify PASS. No release branch merge or GitHub push occurred; GitHub credentials were unavailable. The dedicated branch was updated in the local repository.

Next session: repair the Stage 2 HIR worker crash with a fresh bounded verification budget; obtain admitted current-source compiler evidence; run the Item 6 CAS and production edit acceptance; complete Item 5 provider/size/startup gates and Item 6 time/RSS gates; then review and land on `release/1.0`.

## Continuation

The subsequent production call-site repair passed Stage 2 naming sanity. Compiler-test delegation and Item 5/6 qualification remain open; see [the continuation report](item56_release_continuation_2026-10-10.md).
