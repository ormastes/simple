---
paths:
  - "**"
alwaysApply: false
---
# Version Control

- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `sh scripts/check/land.shs` — gates the rules.sdl quick-group and integrity
  checks against COMMITTED content, THEN runs `sj bookmark set main -r @- && sj
  git push --bookmark main`. **Do not push via raw `sj`/`jj git push` directly** —
  `jj git push` never invokes `.git/hooks/pre-push`, so the rules.sdl gates are
  silently skipped on that path. See
  `doc/08_tracking/bug/jj_push_bypasses_rules_sdl_gates_2026-08-11.md`.
- Fetch: `sj raw jj git fetch && sj raw jj rebase -d main@origin`

## When `jj git push` fails ("External git program failed")

Origin's HTTPS token is dead. Push the rebased tip directly over SSH, then re-sync tracking:

```bash
TIP=$(jj --ignore-working-copy log -r '@-' --no-graph -T 'commit_id')
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git push git@github.com:ormastes/simple.git "$TIP":refs/heads/main
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" jj --ignore-working-copy git fetch
```

Always verify with `git ls-remote` after — a clean-looking exit is not proof the content landed.

## Rebase conflict loop (root-first)

Parallel agent sessions force-push main continuously; a rebase can conflict a whole chain. Never resolve at the tip — resolve the ROOT and let descendants auto-rebase, looping until empty:

```bash
jj --ignore-working-copy log -r 'roots((main@origin..@) & conflicts())'   # find root
jj --ignore-working-copy restore --from <chosen-side> --to <ROOT> <paths...>
```

Side policy is per-path: paths whose latest truth is local restore from the pre-rebase local tip sha; paths already superseded upstream restore from `main@origin` (verify by symbol-grep on origin first). `--ignore-working-copy` is required — it skips the WC snapshot and dodges "Concurrent checkout" races.

## Pre-push guards

### What actually runs on a push (measured 2026-08-23 — read this first)

Until 2026-08-23 this file stated verbatim that several guards below were
"Wired into `pre-push-conflict-tree-guard.shs`", and called some MANDATORY. They
were not wired anywhere. The hook does not run guards itself: it `exec`s
`scripts/check/check-push-must-pass.shs`, which runs **exactly the `push`-tier
rows of `config/check/must_check_gates.sdn`** and nothing else. A guard absent
from that file runs on no push, whatever any prose says. A doc that claims
enforcement which does not exist is worse than no doc — that is how
`check-type-walk-constructor-parity.shs` sat unenforced for a day while its bug
record claimed it existed, and it is the same class as the parse-shard revert
that cost ~18 GB of RSS per stage1 run.

**Enforced, blocking, verified by executing the real push path** (a ref row fed
to `check-push-must-pass.shs`, each verdict line observed):

| row id | guard | measured verdict | cost |
|---|---|---|---|
| `push-conflict-tree` | `check-no-conflict-tree-push.shs` | PASS | <1s |
| `push-tree-size` | `check-tree-size-push.shs` | PASS | <1s |
| `push-conflict-markers` | `check-no-conflict-markers-push.shs` | PASS | <1s |
| `push-rules-quick` | `check-rules-sdl.shs --group quick` | PASS — 11 gates | ~3s |
| `push-interpreter-module-owners` | `check-interpreter-module-owners.shs` | PASS — 13 modules | <1s |
| `push-runtime-api-regression` | `check-runtime-api-regression-push.shs` | PASS — 2821 symbols, 0 removed | <1s |
| `push-c-runtime-compiles` | `check-c-runtime-compiles-push.shs` | PASS — 117 compiled | 25s |
| `push-no-direct-rt` | `check-no-direct-rt.shs` | PASS — forbidden=11783 | 8s |
| `push-signature-type-import-provenance` | `check-signature-type-import-provenance.shs` | PASS — 1810 files | 7s |
| `push-type-walk-constructor-parity` | `check-type-walk-constructor-parity.shs` | PASS — 11 constructors | <1s |
| `push-perf-regression-tests` | `check-perf-regression-tests.shs` | PASS — 131 mechanisms | 1s |
| `push-process-wait-eintr-retry` | `check-process-wait-eintr-retry.shs` | PASS — 3 checks | 3s |
| `push-guard-wiring` | `check-guard-wiring.shs` | PASS — 871 guards, 0 NEW unwired | 39s |

Total ~90s. `push_blocking` in the manifest is now honoured rather than parsed
and discarded: `false` runs the guard and RECORDS its verdict on stderr
(`push-must-check: ADVISORY <id> verdict exit=<rc>`) without failing the push.
Advisory is never a pass and is never silent. Adding a guard needs BOTH a
manifest row and a `case` arm in `check-push-must-pass.shs` — an unrecognised
row is a hard error, never a silent skip.

**NOT enforced on any push, with the reason** (run these by hand; do not read
their bullets below as claims of enforcement):

| guard | measured on `origin/main` | why not wired |
|---|---|---|
| `check-cow-alias-hotpath.shs` | PASS — 9674 files, 198 offenders, 0 new | 226s; too costly for every push. CI/manual lane. |
| `check-core-lib-purity.shs` | **FAIL** — 18 new violations, 1 stale baseline | honestly RED; wiring it would block every push on someone else's debt |
| `check-seed-extern-registry.shs` | **FAIL** — 2 new unregistered (`rt_smf_reader_`, `rt_text_eq_any`) | honestly RED |
| `check-bodyless-block-parity.shs` | ERROR — no executable at `bin/simple` | needs a deployed compiler; ERRORs in a clean tree |
| `check-unbacked-extern-ratchet.shs` | ERROR — census needs `bin/simple` | same |
| `check-stage-binaries-runnable.shs` | ERROR — no tracked stage binary in tree | needs the bootstrap artifacts; also RED where they exist |
| `check-no-unresolved-runtime-symbols.shs` | RED (83 undefined codegen names) | blocked on a bootstrap redeploy |
| `check-seed-builds-push.shs` | — | needs a warm `CARGO_TARGET_DIR` and a 1-2 min budget on the pushing machine |

Each becomes a one-line change (manifest row + `case` arm) the day its blocker
clears. Do not promote one by editing prose.

**`check-guard-wiring.shs` reachability is not the same claim.** It uses a
deliberately BROAD textual model — any mention of a guard's basename by a
reachable file counts as an edge — so it reports "invoked" for guards that are
merely NAMED in a comment of something that runs. Its `guard_invoked` count
answers "is this guard referenced from a root at all", not "does this run on a
push". Only the table above answers the second question.

**Run them from the REPO ROOT of a real clone.** Until 2026-08-01 both guards
failed open on the working directory: from a `git archive` worktree under
`/dev/shm` or `/run/user/1000` (no `.git`) they printed `nothing to push` and
**exited 0 without checking anything**. They now exit **2** instead. The third
guard, `check-tree-size-push.shs` (added 2026-08-01), was built fail-closed on
cwd from the start and is verified from exactly that archive worktree. Read the
verdict line, which is always the last line of stdout:

| verdict | exit | meaning |
|---------|------|---------|
| `PASS — <n> commit(s)/file(s) checked ...` | 0 | safe; `n` is always > 0 |
| `FAIL — ...` | 1 | do not push |
| `ERROR — nothing was checked` | 2 | could not determine; do not push |

`OK` is no longer emitted — a passing run always states how many commits or
files it actually examined, so a vacuous run cannot be mistaken for a real one.
An explicitly-supplied range that resolves to 0 commits is an ERROR, not a pass.
A bare revision (no `..`) is rejected rather than silently reinterpreted.
Details and the fixture-based proofs:
`doc/08_tracking/bug/pre_push_guards_fail_open_on_cwd_2026-08-01.md`.

- **No `.jjconflict-*` trees in the outgoing range — run `sh scripts/check/check-no-conflict-tree-push.shs` (exit 0 = safe).** With no argument it checks `main@origin..@-`, exactly what `jj git push --bookmark main` sends. **`jj git push` does NOT block a conflict commit**; on 2026-07-25 one was pushed and `main` carried no source files at all across two commits until it was repaired. A jj conflict commit's git tree contains *only* `.jjconflict-base-0/` and `.jjconflict-side-N/`, so a clone gets an empty repo. Symptom to recognise: `git cat-file -p <sha>:<path>` says *"exists on disk, but not in <sha>"* — that reads like one missing file but means the whole tree is gone; confirm with `git ls-tree --name-only <sha>`. Range only — never `main@{0}` (that sweeps the whole reflog).
- **No literal conflict-marker text in pushed file content — run `sh scripts/check/check-no-conflict-markers-push.shs` (exit 0 = safe).** Same default range as the tree guard. This catches a different failure than the one above: a `jj rebase` can inject conflict-marker text into file CONTENT (both jj's `<<<<<<< conflict N of M` / `%%%%%%%` / `>>>>>>> ... ends` style and git's classic `<<<<<<< HEAD` / `=======` / `>>>>>>>` style) without the commit being tree-conflicted, so the tree guard misses it. On 2026-07-30 exactly this happened: a rebase wrote markers into 38 tracked files, including the Rust seed `src/compiler_rust/runtime/src/value/mod.rs`, breaking every seed build. The guard flags a file only when it has a matching open+close marker pair, so prose that merely mentions marker syntax (e.g. this file, jj's own vendored docs) doesn't false-positive.
- **No structurally wrong tree in the outgoing range — run `sh scripts/check/check-tree-size-push.shs` (exit 0 = safe).** Same default range as the two guards above. This is the gate that the other two cannot be: they only recognise `.jjconflict*` entries and literal marker text, so a tree truncated for any OTHER reason — a git index truncated by ENOSPC, an API `base_tree` landing that silently inherited an already-wiped base — passes both. `main` was wiped to near-zero files **twice in 24 hours** that way (`118c636ead8`: 109,375 files → 4) with every guard green; the only thing that ever caught it was a human counting `git ls-tree -r --name-only $C | wc -l`. Four fail-closed checks: **size band** (±0.15% of the base the push replaces, *plus* an absolute 90,000/150,000 floor and ceiling — the absolute floor is the only check that fires when the BASE is itself already wiped and the delta is therefore zero); **duplicate tree entries** (a real corruption listed `src/lib` twice at **109,815 files — higher than the healthy 109,543** — so a floor-only check is blind to it; `git fsck` is authoritative but takes >2min here, use it for investigation not gating); **`src/` entry band** 13..25 (measured 15, the corruption showed 9 — the strongest single signal); and **load-bearing path floors** (`src/runtime ≥ 150` — measured 185, corruption showed 0, a proven canary. `src/std` is NOT a canary: it holds one file, so a non-empty test on it is vacuous). A lane that legitimately moves more than the band allows states `--expect-files <n>`, which RECORDS the expected post-count in the verdict and recentres the band — every other check still applies, and there is no flag or env var that turns one off. `--selftest` runs before every scan and is fatal (14 fixtures). Proofs, including a real `git push` where the duplicate-entry fixture was blocked by this guard ALONE: `doc/08_tracking/bug/no_automated_tree_size_gate_2026-08-01.md`.
- **No unbaselined test-tree divergence in the pushed commit — run `sh scripts/check/check-test-tree-divergence.shs --ref <NEW>` (exit 0 = safe).** `<NEW>` is the exact commit being pushed — the guard reads COMMITTED content via `git ls-tree`/`cat-file`, never the shared working copy, so it works on a plumbing-built commit that was never checked out. This is the fourth mandatory pre-push check: it fences the LIVE duplicate test trees (`test/01_unit/` vs `test/unit/`, `test/02_integration/` vs `test/integration/`) against the baseline in `scripts/check/test_tree_divergence_baseline.txt`, failing on any NEW divergence or any baselined pair that is now identical (stale baseline). Until 2026-08-10 only the git pre-push hook (`pre-push-conflict-tree-guard.shs`) ran it — every plumbing landing bypassed it, which is exactly how divergence sat RED for days with nothing acting. Same verdict convention as the other three: `PASS — <n> pairs checked, ...` with n > 0, `FAIL` exit 1, `ERROR — nothing was checked` exit 2; a run that compares 0 pairs is an ERROR, not a pass. Do not "fix" a FAIL with `--generate-baseline` without reading the diff — that flag exists only for deliberate, reviewed baseline updates.
  **Scoped-delta escape (this guard ONLY — the other three have no escape, and "3 of 4 passed" is never a licence):** a pre-existing red left by another session must not block landings that introduce zero new divergence, but stepping over it silently is exactly how the divergence backlog accumulated. The escape is mechanical, not a judgement call: run `sh scripts/check/check-test-tree-divergence-delta.shs <BASE> <NEW>` (BASE = the origin tip your push replaces). It runs the guard in `--ref` mode for BOTH sides — never the working copy, which disagrees with committed content under concurrent load (910 vs 859 diverged measured 2026-08-10) — and diffs the offender lists byte-for-byte, verdict as the last stdout line: `PASS — <n> pre-existing offender(s), 0 introduced by this range` exit 0 / `FAIL — <n> newly introduced: <names>` exit 1 / `ERROR — nothing was checked` exit 2. Landing on a delta-PASS additionally REQUIRES recording the pre-existing offender list (the helper saves it and prints the path) in the commit message or a `doc/08_tracking/bug/` record — an unrecorded step-over is a violation even when the delta is clean. Any range that changes the offender list or any offender category (new divergence, mirror-only, stale allowlist, stale baseline) stays hard-blocked, including every range that touches the test trees non-identically; there is no flag that widens this, and no directory is exempt.
- **The Rust seed must still compile — run `sh scripts/check/check-seed-builds-push.shs` (exit 0 = safe).** Same default range as the guards above. This closes a gap none of them cover: they all check tree STRUCTURE (conflict trees, marker text, tree size, test-tree divergence, revert patterns) — none of them compiles anything. Incident 2026-08-11: `origin/main` was found unbuildable — `cargo build --release --bin simple` in `src/compiler_rust` failed with unresolved-import (E0432) and missing-enum-variant (E0599) errors from two independent incomplete changes that landed hours apart, and every existing guard passed because a structurally clean tree can still fail to compile. Mechanism **(changed 2026-08-18 — the old path filter was FAIL-OPEN; see below)**: the guard digests the seed's own CONTENT at the new tip (the git tree object ids of `src/compiler_rust` and `src/runtime` plus the `Cargo.lock` blob id) and skips compiling **only** when that exact content has already been recorded green by a previous run of this guard (marker dir `$SEED_GREEN_MARKER_DIR`, default `/mnt/data/.seed-build-guard-green`, written only after a genuine green compile; deleting it is always safe and merely forces recompilation). The files-changed count is still reported for non-vacuity — a docs-only push reports `n > 0`, never `n = 0` — but it no longer *decides* anything. Otherwise the guard materialises the NEW tip into an isolated `git worktree add --detach` (never the shared, contested working copy) and runs `cargo check --release --bin simple` — deliberately `check` not a full `build`: `check` runs the complete frontend (parse/resolve/type-check/borrow-check) and only skips codegen+link, so it catches E0432/E0599-class errors identically to `build` while being materially cheaper; the guard's own `--selftest` proves this by `cargo check`ing a fixture with a deliberate unresolved import and a nonexistent enum variant and asserting both the FAIL and the exact `E0432`/`unresolved import` text, plus a clean sibling fixture that must PASS. Uses a dedicated `CARGO_TARGET_DIR` under `/mnt/data` (fast NVMe, not the space-constrained root fs), reused warm across runs; `KEEP_BUILD_DIR=1` keeps the worktree for debugging. **Why the path filter had to go (incident 2026-08-18, `doc/08_tracking/bug/origin_main_unbuildable_missing_half_1e40de916bb_2026-08-18.md`):** `origin/main` sat unbuildable again — E0432 at `compiler/src/interpreter_call/core/function_exec.rs:10` (importing `module_globals_generation`, which existed nowhere at origin) and E0599 at `compiler/src/interpreter_sffi.rs:125` — while every push over it reported PASS, because origin's tip commits were docs-only and the filter short-circuited without compiling anything. The filter's inference ("the range didn't touch the seed, so buildability cannot have REGRESSED") is true and beside the point: it presumes the base was green, and nothing ever established that, so one broken base launders every later docs-only push into a green verdict. This is the same fail-open `check-c-runtime-compiles-push.shs` avoided by being tree-scoped. The fix keeps a fast path (a full `cargo check` is 1-2 min warm on this host and this guard runs on every push; a guard that is routed around with `--no-verify` protects nothing) but rests it on a **positive proof** — "this exact seed content was compiled and passed" — instead of an absence. Content-keying rather than commit-keying matters because shas churn constantly under rebase, so a per-commit green cache would almost always miss. Verified against reality: on the real broken tip the guard now says `FAIL — cargo check failed in e9e22a1230f: error[E0592]: duplicate definitions with name INLINE_INT_BITS` (exit 1) for the *docs-only* range `e9e22a1230f~1..e9e22a1230f`, and PASSes on the tree carrying the missing half `1e40de916bb`.

Same verdict convention as the others: `PASS — <n> file(s) checked, seed bin + test targets compile cleanly at <sha> (seed content <digest> recorded green; ...)` (or `... seed content <digest> at <sha> byte-identical to a tree this guard already compiled green (<timestamp>)` on the fast path) exit 0 / `FAIL — cargo check failed in <sha>: <first error>` exit 1 / `ERROR — nothing was checked` exit 2; a 0-files range is always ERROR. `--selftest` runs before every scan and is fatal (**5 fixtures** as of 2026-08-18). **NOT ENFORCED (measured 2026-08-23): run it by hand.** It is in no push-tier row of `config/check/must_check_gates.sdn`, so nothing runs it on a push; wiring it needs a warm `CARGO_TARGET_DIR` on the pushing machine and a 1-2 min budget, which the push path does not have today. See `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`.
- **No mass exported-runtime-API deletion — run `sh scripts/check/check-runtime-api-regression-push.shs` (exit 0 = safe).** Same default range as the guards above. Incident 2026-08-11: commit `6e2f613d302`, titled "fix(runtime): preserve u64 across erased values", was a stale-snapshot clobber that silently DELETED 44 runtime functions (-1896 lines from `value/collections.rs`, -156 from `value/sffi/value_ops.rs`) — the whole `rt_string_*` API, array ops (push/pop/sort/find/take/map/reduce/reverse), `rt_collection_remove`, `rt_value_unbox_int` — and every existing guard passed: the size guard bands on file COUNT, not symbols inside existing files; the revert guard needs an exact-blob match against ONE prior commit, and this was a stale-forward snapshot, not an exact revert. Mechanism: extracts the DEFINED `rt_*` symbol set from committed content only (`git show <rev>:<path>`) at both range endpoints, across the Rust runtime (`src/compiler_rust/runtime/src/**/*.rs`, `pub extern "C" fn rt_*` / `pub fn rt_*`) and the C runtime (`src/runtime/*.c`/`*.h`, incl. baremetal stubs, `rt_NAME(...) {` definitions) — evaluated as **separate** sets, never unioned, because they are parallel implementations of the same names and unioning them was tried and found to mask real Rust-only removals when a same-named C fallback still existed. FAILs when >=5 symbols are removed in one push (matches `check-no-revert-push.shs`'s `--min-files=5` precedent: a handful of intentional removals is routine, 44 is not), OR — no escape, ever — when a removed Rust symbol is still `pub use`-re-exported in `runtime/src/lib.rs` (unbuildable crate, detected statically without invoking cargo). Escape for the count check only: `--expect-removals <n>`, which RECORDS the accepted count in the verdict line and recentres the threshold for that push, same philosophy as the size guard's `--expect-files`. Verdict: `PASS — <n> symbol(s) checked, 0 removed` exit 0 / `FAIL — <n> symbol(s) checked in <range>, <k> symbol(s) removed: <names>[; <m> still re-exported in lib.rs (unbuildable): <names>]` exit 1 / `ERROR — nothing was checked` exit 2; a 0-symbol range is always ERROR. `--selftest` runs before every scan and is fatal (4 fixtures: incident-replay must FAIL naming the removed+unbuildable symbols, forward-progress must PASS, a single below-threshold removal must PASS, empty range is checked for `EV_CHECKED==0`). Validated directly against the real incident: `sh scripts/check/check-runtime-api-regression-push.shs '6e2f613d302~1..6e2f613d302'` FAILs, naming 45 removed `rt_*` symbols and flagging the unbuildable set. **ENFORCED on push (measured 2026-08-23)** as manifest row `push-runtime-api-regression` in `config/check/must_check_gates.sdn`, executed by `check-push-must-pass.shs` over the outgoing range; verdict `PASS — 2821 symbol(s) checked, 0 removed` (<1s).
- **MANDATORY (promoted 2026-08-11): the C runtime must compile — run `sh scripts/check/check-c-runtime-compiles-push.shs` (exit 0 = safe).** This is the seventh guard and the first that runs a COMPILER. Incident 2026-08-11 (`doc/08_tracking/bug/runtime_native_c_uncompilable_unsigned_box_never_implemented_2026-08-11.md`): `src/runtime/runtime_native.c` used the type `RtCoreUInt` and the functions `rt_core_as_heap_uint` / `rt_value_u64` at 8 sites with **zero declarations anywhere in the tree** — `clang -fsyntax-only` fails outright, so that file had **never** compiled — and it sat in `main` looking green. It looked green because every other guard is a text-and-tree check: conflict-tree entries, conflict-marker text, file counts, test-tree diffs, blob-vs-history comparison, and `rt_*` symbol-set deltas. Source that is well-formed as BYTES, non-conflicted, correctly sized, forward-moving, and symbol-preserving passes all six while being complete nonsense to a compiler. Note especially that `check-runtime-api-regression-push.shs` greps for `rt_NAME(...) {` **definitions** and is therefore blind to a *use* of a symbol that was never defined — the exact defect here. Mechanism: `$CC -fsyntax-only` (parse + semantic analysis, no codegen, no linking, no CMake, no SDL/OpenSSL/SQLite dev packages, seconds not minutes) over every `*.c` under `src/runtime/` excluding vendored code per CLAUDE.md's Owned-Code Scope (`src/runtime/vendor/**`, `miniaudio.h`, `stb_image.h`, `stb_truetype.h`). **The compiler's exit status is read directly into a variable on the line after the invocation — never through a pipe**, since a pipeline's `$?` is `tail`/`grep`/`head`'s status and has produced false greens in this repo before. Three-way classification: exit 0 = compiled; exit≠0 where every error is a missing header that does **not** exist in the repo = SKIP (an external SDK such as `wasmtime.h` is not installed here — reported separately, never counted as compiled, never a pass); anything else = FAIL, including a missing header that DOES exist in-repo, because that is a broken include path and a real defect. Verdict: `PASS — <n> file(s) compiled, 0 errors` exit 0 / `FAIL — <n> file(s) failed to compile: <names>` exit 1 / `ERROR — nothing was checked` exit 2. Non-vacuity is absolute — a run that fed 0 files to a compiler is ERROR, and **a machine with no `clang`/`cc`/`gcc` is ERROR, never a pass**: absence of a compiler is absence of evidence. `--selftest` runs before every scan and is fatal (8 fixtures: well-formed must-PASS; undeclared-TYPE and undeclared-FUNCTION must-FAIL replaying the incident's exact shape; unknown external header must-SKIP; an in-repo header off the include path must-FAIL *not* skip; plain syntax error must-FAIL; an empty tree must yield 0 compiled so the caller is forced to ERROR; a deliberately broken `.c` under `vendor/` must not be scanned at all). Scope note: unlike the range-based guards this one checks a TREE (`--root DIR`, default the working tree), not a `BASE..NEW` delta — compilability is a property of a tree, since a push that edits only a header can break a `.c` it never touched, so a changed-files-only scan would be fail-open. Known limit, stated rather than papered over: `-fsyntax-only` does not link, so a declared-but-never-defined symbol still gets through. **Promotion history:** landed advisory 2026-08-11 at `04848434af0c` because it was honestly RED on `main` — `src/runtime/platform/async_linux_uring.c` failed with `use of undeclared identifier 'NULL'` at line 733 (missing `#include <stddef.h>` in its `!SPL_HAS_IO_URING` stub branch). Fixed same day by adding the include; the guard now reports `PASS — 96 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)` (the two skips are `counterpart_worker_runtime.c` and `scv_wasm_shim.c`, both genuine external-SDK-header SKIPs, never counted as compiled). **ENFORCED on push (measured 2026-08-23)** as manifest row `push-c-runtime-compiles`; verdict `PASS — 117 file(s) compiled, 0 errors (2 skipped)` in 25s.
- **Direct `rt_*` call-site ratchet — run `sh scripts/check/check-no-direct-rt.shs` (exit 0 = safe).** Not a tree-structure guard like the others above — it is a RATCHET on Simple product code (`*.spl` under `src/`, excluding `vendor/`), not a hard zero-bar: it counts direct `rt_*(...)` call sites, splits them into allowlisted-provider vs. forbidden-product using `scripts/check/no_direct_rt_allowlist.txt`, and FAILs only when the forbidden count exceeds the recorded baseline in `scripts/check/no_direct_rt_baseline.txt`. Measured 2026-08-18: `PASS — 14796 file(s) scanned, forbidden=12948 (baseline 12948)`. `--critical` (or `SIMPLE_RT_CRITICAL=1`) switches to a stricter mode where ANY forbidden call site fails, for use on critical/mission-critical build lanes. Selftest runs first, unconditionally, and is fatal. **ENFORCED on push (measured 2026-08-23)** as manifest row `push-no-direct-rt`; verdict `PASS — 15203 file(s) scanned, forbidden=11783 (baseline 11783)` in 8s.
- **ADVISORY (added 2026-08-18, honestly RED — see below): tracked stage binaries must actually run — run `sh scripts/check/check-stage-binaries-runnable.shs` (exit 0 = safe).** This is the eighth guard and the first that EXECUTES a tracked artifact. Incident 2026-08-18 (`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`): the git-tracked binary `bootstrap/stage3/simple` SEGVs (rc=139) on a three-line hello world, for **both** of the two commands it supports, while `--version` answers cleanly — which is exactly why it looked healthy. Every guard above passed over it, because every one of them checks trees, ranges, or source: conflict entries, marker text, file counts, test-tree diffs, blob-vs-history, `rt_*` symbol sets, and C that parses. Even `check-c-runtime-compiles-push.shs`, the only one that runs a compiler, runs it over SOURCE. A binary blob is opaque to all of them: correctly sized, non-conflicted, forward-moving, symbol-preserving — and stone dead when you run it. Mechanism: enumerates every git-**tracked** file named `simple` under `bootstrap/` via `git ls-files` (never a hardcoded list, so a new stage is covered the day it lands), materialises it (working-tree file by default; committed content via `git cat-file blob <rev>:<path>` when `--rev` is given **or** the tracked path has no working-tree file, so a locally-deleted artifact is exercised rather than silently skipped), and runs each supported command on a three-line hello world in a private temp dir under `timeout`. **The exit status is read DIRECTLY into a variable on the line after the invocation, never through a pipe** — a pipeline's `$?` is the last command's status and has produced false greens in this repo. Classification: rc 0 = OK; rc >= 128 or 124 = CRASH (139 = SEGV, 134 = abort, 124 = timed out); any other non-zero = FAIL; crashes and failures are both offenders, named separately in the verdict. **Command scope is exactly `compile` and `native-build`, and must stay that way:** stage binaries are the BOOTSTRAP cli (`src/app/cli/bootstrap_main.spl`, dispatch at lines 459-492), which deliberately exposes only those two — it has no `run`, `test`, `lint`, `fmt` or `build`, so probing for them is a category error that has already misled one investigation. `--version` is probed only as a liveness precondition; a passing `--version` is explicitly **not** a pass, since that is the exact thing that hid the incident. Verdict: `PASS — <n> invocation(s) executed across <k> binary(ies), 0 crashes` exit 0 / `FAIL — <n> invocation(s) executed across <k> binary(ies), <m> crashed/failed: <names>` exit 1 / `ERROR — nothing was checked (<reason>)` exit 2. Non-vacuity is absolute: a run that executed 0 binaries is ERROR, and **finding no tracked stage binary at all is ERROR, never a pass** — absence of an artifact to test is absence of evidence. A tracked path whose content cannot be materialised is likewise ERROR; a tracked artifact that is not executable is an offender, not a skip. `--selftest` runs before every scan and is fatal (6 fixtures, all built as real executables probed by the real scanner: a working fake must PASS; a fake that SEGVs on `compile` while `--version` succeeds must FAIL, replaying the incident's exact shape; a plain non-zero exit must FAIL; a fake whose `--version` itself crashes must FAIL; a non-executable tracked artifact must FAIL; a repo with no stage binary must execute 0 invocations so the caller is forced to ERROR). Scope note: like the C-runtime guard and unlike the range-based guards, this checks a TREE (`--root`/`--rev`), not a `BASE..NEW` delta — runnability is a property of an artifact, and the incident binary was untouched by the push that would have shipped it. Known limit, stated rather than papered over: it proves the commands do not crash, not that their output is correct. **Landed ADVISORY because it is honestly RED on `main`**: measured 2026-08-18, `FAIL — 12 invocation(s) executed across 4 binary(ies), 8 crashed/failed` — **all four** tracked stage binaries (`bootstrap/stage1/simple`, `stage2/simple`, `stage3/simple`, `stage3/x86_64-unknown-linux-gnu/simple`) SEGV on both commands, which is broader than the filed bug record's stage3-only scope. Repair needs a bootstrap redeploy, which is blocked separately; promote this guard to MANDATORY once that lands and it goes green.
- **ADVISORY (added 2026-08-21): no unresolved runtime symbols — run `sh scripts/check/check-no-unresolved-runtime-symbols.shs` (exit 0 = safe).** Sibling of the stage-binaries guard above and the same incident (`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`): codegen emitted a call to `rt_unwrap_or_trap`, the C runtime never defined it, the native link tolerated the undefined symbol (bootstrap logs even printed "Unresolved symbol preview: ...") and the NULL GOT slot became a SIGSEGV. `-fsyntax-only` never links, and the extern ratchet classifies Simple `extern` declarations, not codegen-emitted calls, so neither could see it. Two checks: undefined runtime-prefixed symbols in each tracked `bootstrap/**/simple` (`nm -u` + `nm -D`, minus what the binary's own `ldd`-resolved libs define, prefixes derived from `src/runtime/runtime.h`), and — before any link — every codegen-emitted runtime entry name missing from `build/simple-core/libsimple_runtime.a`. Same verdict convention; 0 artifacts **in total**, missing `nm`, a stripped artifact with no symbol table, or a STALE archive is ERROR, never a pass — but zero *binaries* alone is a reported `binaries=none(...)` status, not a verdict, since `git ls-files bootstrap` now returns 0 rows and the old hard exit there made the guard ERROR before ever judging the archive (fixed `54e12925034`). `--selftest` fatal (6 fixtures; (f) is the archive-without-binaries case with a negative control). **The archive half is now GREEN** — re-measured 2026-08-23 against a freshly built core-C capsule: `PASS — 196 symbol(s) checked across 0 binary(ies) + archive, 0 unresolved`; the "83 undefined" figure was stale. Still ADVISORY only because the binary half has no artifact to judge: the stage blobs are untracked, and the ones that were tracked were stripped. Promote once a redeploy produces an unstripped stage binary.
- **No NEW unbacked extern declarations — run `sh scripts/check/check-unbacked-extern-ratchet.shs` (exit 0 = safe).** Stage 3 of `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`: an extern with no runtime backing silently returns nil instead of failing, and the tree already carries 1,466 such symbols, so the population cannot be made fatal at once. This guard freezes them in `scripts/check/unbacked_extern_baseline.txt` and fails any push that ADDS one. Classification is delegated to `scripts/check/extern-backing-census.shs` (the single source of truth, which reads DEFINED symbol tables out of real link artifacts via `nm`, not text-grep), and the frozen set is the **union** of the census classes `GENUINELY_MISSING` and `DEAD_DECLARATION` — never `GENUINELY_MISSING` alone: Stage 2 verified all 262 `DEAD_DECLARATION` symbols and **zero** were dead (70 have a real `.spl` call site in another file, 41 have non-`.spl` references, 111 are documented public API), so baselining only the 1,203 would ratchet live public API straight to fatal. Same rule as the test-tree divergence guard in both directions: a baselined symbol that is no longer unbacked (became backed, or its declaration was removed) is a **stale baseline** and also FAILs, because a baseline that no longer describes the tree is how a ratchet silently stops ratcheting. Verdict convention identical to the guards above: `PASS — <n> unbacked extern symbol(s) checked, 0 new, 0 stale` exit 0 / `FAIL — <n> symbol(s) checked, ...` naming every offending symbol exit 1 / `ERROR — nothing was checked` exit 2; a 0-symbol comparison is always ERROR, and a missing deployed binary or a failed census is ERROR, never a pass. `--selftest` runs before every scan and is fatal (4 fixtures: clean must PASS; a new unbacked symbol must FAIL naming it; a baselined-but-now-backed symbol must FAIL as stale; an empty scan must ERROR). Deliberate-update path: `--generate-baseline` — **for reviewed updates only, exactly like the divergence baseline's `--generate-baseline`. Do not "fix" a FAIL with it without reading the diff**; a FAIL naming new symbols is real new debt, and regenerating hides it. Runtime ~20s. Does not flip any default and deletes no declaration — Stage 2 proved deletion unsafe.
- No leaked markers in previously-conflicted files: `git grep -c '^<<<<<<<' $TIP -- <paths>` must be 0.
- Stale `.git/index.lock` with no live holder: `find .git/index.lock -mmin +5 -delete`. Check `pgrep -af 'jj (rebase|restore)'` first — a D-state jj may still be progressing (verify via `/proc/PID/io` deltas) and must not be killed.
- Edit-tool changes are not auto-snapshotted: commit immediately after editing, and re-verify file content (`grep`) after any `workspace update-stale` — a parallel-session reconcile can silently clobber uncommitted edits.

## Standalone origin-health watchdog (NOT an eighth pre-push guard)

`sh scripts/check/watch-origin-tree-health.shs` is a pull-based safety net,
distinct in kind from the five pre-push guards above. The guards run (or are
supposed to run) synchronously on push and can block one; the watchdog never
runs on push, never blocks a push, and never mutates refs — it only FETCHES
origin/main read-only, on a timer, and inspects whatever tip is actually
there. It exists because detection of a wipe must not depend on the pusher's
hooks having run: `doc/08_tracking/bug/fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`
found that a stale `core.hooksPath` plus a non-executable hook file silently
downgraded every guard above to advisory for a real push, and the wipe was
only found by luck.

```bash
sh scripts/check/watch-origin-tree-health.shs --once                # single check, verdict + exit code
sh scripts/check/watch-origin-tree-health.shs --once --rev <sha>    # check an explicit rev, no fetch
sh scripts/check/watch-origin-tree-health.shs --watch [interval_s]  # loop (default 300s), alerts on state CHANGE only
```

Same verdict convention as the guards: `PASS — <n> invariant(s) checked,
origin/main healthy (<files> files)` exit 0 / `FAIL — ...` exit 1 / `ERROR —
nothing was checked` exit 2. Thresholds (90,000/150,000 absolute file-count
band, `src/` entry band 13..25, `src/runtime >= 150` canary) mirror
`check-tree-size-push.shs` — that script is the source of truth; the
watchdog's `--selftest` cross-checks the two files' literal values so they
cannot drift apart silently. On detecting a bad tip it prints the exact
restore recipe (temp-index read-tree from the healthy parent, fast-forward
`commit-tree`, push) but never runs it — it only alerts, never auto-restores.
No cron/systemd unit is installed by default; running it continuously is an
operational choice for whoever owns the watching machine.

## Sync must never clobber (anti-revert protocol)

Hourly/periodic "sync" commits (e.g. `chore(sync): session work products`) have
repeatedly REVERTED other sessions' landed fixes by snapshotting a **stale**
whole working copy and pushing it — while falsely claiming "fixes preserved at
origin versions". A sync that reverts is worse than no sync. Mandatory:

1. **Rebase before you snapshot.** `sj raw jj git fetch && sj raw jj rebase -d
   main@origin` FIRST, resolve, and only then snapshot the WC. Never commit a WC
   captured before the latest fetch.
2. **Never whole-WC-commit files this session didn't change.** A sync commit
   carries only files THIS session actually authored. Do not `jj commit -a` /
   `git add -A` a full stale tree. Scope the commit to your changed paths.
3. **Revert guard (blocks the push).** For every file in the outgoing range,
   confirm the change is a forward delta, not a rewind of someone else's fix:
   `git diff main@origin..$TIP -- <path>` must not restore an older version of a
   file you didn't touch. If any hunk reintroduces code origin already moved past
   (symbol-grep origin to confirm), STOP and drop that path — do not push.
4. **Never write "fixes preserved at origin versions"** unless you verified it by
   symbol-grep on `main@origin` for each fix. An unverified preservation claim is
   how the last three clobbers hid themselves.

Non-code artifacts (docs, skills, workflows, spipe state) may sync freely; the
danger is only `src/**`, `scripts/**`, and other product code — hold those to the
guards above. Upgrade path: a `scripts/check/` pre-push hook that fails when the
outgoing range reverts a product file the committer didn't author. (The
conflict-tree half of this is now implemented as
`scripts/check/check-no-conflict-tree-push.shs`; the revert-detection half is
still manual.)

**Rebasing onto a parallel session's resolution: diff both directions.** When
two sessions fix the same file, the newer origin version is not automatically a
superset. On 2026-07-25 origin's resolution of `make_os_disk.c` kept most of the
local fixes but replaced fixed-cluster geometry with dynamic sizing — so the
local copy was *behind* on one axis and *ahead* on three. Overwriting either way
would have reverted real work. Check `diff -u origin_version local_version` and
read **both** the `-` and `+` sides before choosing; often the answer is that
origin already supersedes you and the right move is to drop your commit.

## LLM wiki before commit

Before committing feature work, refresh the related LLM wiki entries so the
commit ships with current knowledge links: the affected
`doc/00_llm_process/feature_expert/<feature>/skill.md` and
`doc/00_llm_process/layer_expert/<layer>/skill.md`. Templates:
`.spipe/spipe/doc/00_llm_process/template/{feature,layer}_skill.md`. Commit the
wiki update in the same change as the work it describes.
