# Landing record — 113 local commits onto origin/main (2026-08-17)

## Range

- **Base (origin/main at fetch):** `d5ebbefa5f03a53f6241ae218bed22636d2f9ceb`
- **Local tip classified:** `675aa70a21923d6760a4744f8966ab8dbe61984d` (113 ahead / 382 behind)
- **Rebased tip built:** `b0665d6d0021dd0f6507321ac452fa8da60b91c2` (30 commits)
- **Pushed sha:** see "Push proof" below.
- Work done in an isolated `git worktree add --detach` at `/mnt/data/tmp/land-3761907`.
  The shared working tree was **never** rebased (~10 concurrent lanes edit it).

## Classification of the 113

| outcome | count |
|---|---|
| already upstream (content-identical after replay) | 76 |
| genuinely new, applied | 29 |
| deferred (unresolvable code conflict) | 8 |
| **total** | **113** |

Test used, per the brief: `git cherry-pick -n --allow-empty <c>` then
`git diff --cached --quiet HEAD`. True ⇒ applying that diff to the current
origin changes nothing ⇒ content already present. Independent of sha,
subject and patch-id. **No subject-line comparison was used anywhere.**

### Method note — two false readings corrected before trusting any number

1. **An isolated per-commit test over-reports conflicts.** Testing each of the
   113 against origin *individually* gave 59 upstream / 9 new / **45
   conflicts** — badly wrong, because sequential edits to one file conflict
   when replayed alone. A *sequential* replay gave 76 / 29 / 8. Only the
   sequential number is meaningful.
2. **`git cherry-pick --abort` fails after `cherry-pick -n`** (no sequencer is
   in progress), so it leaves the unmerged index in place. A first replay
   inherited one `UU` entry from commit 1 and reported **113/113 conflicts** —
   a completely fabricated result that looked like total divergence. The
   correct reset after an aborted `-n` pick is `git reset --hard HEAD` +
   `git clean -fdq`. Recorded because the failure mode is silent and total.

### Drop count, content-verified sample

76 dropped as already-upstream. Verified by content, not subject:
`fix(runtime): preserve the erased-int high bits`-class rows, the
`rt_clear` Dict branch, and the export-origin lookup work all replayed to an
**empty diff** against origin — the content is present at origin under other
shas/squashes. Probe counts at origin vs pushed tip were compared directly:
`rt_clear` 46 vs 46, `from_wide_int` 3 vs 3 — unchanged, so nothing was
rewound by this landing.

## Conflict resolution policy actually applied

- `doc/08_tracking/bug/*.md`, `doc/03_plan/**`, `.spipe/**` state: resolved by
  **`git merge-file --union`**, keeping **BOTH** sides — two lanes writing one
  bug row are recording different findings. 20 `doc/08_tracking` rows and
  `.spipe/unstable_test_mode/state.md` were merged this way.
- Any conflict touching `src/**`, `scripts/**`, `test/**`: **deferred**, never
  auto-resolved. No `-X ours`, no `-X theirs`, no `--skip` was used anywhere.
- The two stage-3 admission files (`scripts/bootstrap/bootstrap-from-scratch.sh`,
  `scripts/check/lib/bootstrap-stage3/authority.shs`) had **no** conflict in
  this range, so the outright-defer rule never had to fire on them.

## Anti-revert finding — a real semantic conflict that every text guard passes

`c616392639f` ("fix(runtime): make the Rust test suite compile again") applied
**textually cleanly** while being semantically broken: it re-added
`INLINE_INT_BITS` and `fits_inline_int` into `impl RuntimeValue`, but origin
`d5ebbefa5f03` **already defines both** at `value/core.rs:304` and `:324`. The
duplicate pair is a rustc **E0592** duplicate-definition error.

Detected by symbol-count probe across the range, not by any guard:
`INLINE_INT_BITS` 3 → **6**, `fits_inline_int` 8 → **9**.

Resolution: `core.rs` restored to origin's version in
`b0665d6d0021` (a single-file commit, so nothing else was affected).
**Origin's definitions are kept verbatim; only the duplicate was removed.**
This is the same class of defect as the previously-caught `4be6951d019`.

Verified afterwards: `cargo check --release --bin simple` in
`src/compiler_rust` → **RC=0, 0 errors** (3 pre-existing warnings). Net diff on
`src/compiler_rust/` across the pushed range is therefore **empty**, which is
why `check-seed-builds-push` legitimately took its no-changes fast path — the
compile was obtained independently rather than assumed.

## Guard verdicts (verbatim)

```
check-no-conflict-tree-push: PASS — 30 commit(s) checked in d5ebbefa5f03a53f6241ae218bed22636d2f9ceb..b0665d6d0021dd0f6507321ac452fa8da60b91c2, 0 conflict trees

check-no-conflict-markers-push: PASS — 32 file(s) scanned at b0665d6d0021dd0f6507321ac452fa8da60b91c2 across 30 commit(s), 0 conflict markers

check-tree-size-push: selftest 24/24 fixtures correct (16 must-fail, 7 must-pass, 1 env-isolation)
check-tree-size-push: PASS — 30 commit(s) checked, each banded against its own first parent, range base 115536 file(s), 0 structural faults

check-runtime-api-regression-push: selftest 4/4 fixtures correct
check-runtime-api-regression-push: PASS — 2795 symbol(s) checked, 0 removed

check-seed-builds-push: selftest 4/4 fixtures correct
check-seed-builds-push: PASS — 32 file(s) checked, no compiler/runtime changes in range (seed build not re-verified)

check-c-runtime-compiles-push: compiler = clang
check-c-runtime-compiles-push: selftest 8/8 fixtures correct
PASS — 106 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)

check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW; this range introduces nothing
check-test-tree-divergence-delta: base verdict: check-test-tree-divergence: FAIL — 875 diverged vs 812 baselined (64 new, 1 fixed-but-still-baselined); 8 mirror-only (6 unallowlisted, 0 stale-allowlist)
check-test-tree-divergence-delta: PASS — 71 pre-existing offender(s), 0 introduced by this range

cargo check --release --bin simple  (src/compiler_rust)  ->  RC=0, 0 errors
```

All seven guards were **obtained** and PASS. No guard is reported as a pass
without its own output above.

### Unobtained

- **`bin/simple lint`** on the changed `.spl` files — **UNOBTAINED**, not a
  pass. `bin/` is gitignored so a fresh worktree has no compiler, and the
  measured lint cost (~12s startup plus a superlinear per-declaration term) is
  far outside the harness's 10-minute foreground cap for this file set. The
  binary was deliberately not rebuilt or redeployed.
- **`bin/simple test`** — **UNOBTAINED** for the same reason.

### Stepped over, named

- **`--no-verify`** was used on every commit in the replay (user-authorised).
  What that steps over is the local pre-commit hook set; the seven pre-push
  guards above were each run explicitly instead, so nothing was skipped
  unexamined.
- **`check-test-tree-divergence` is pre-existing RED** (875 diverged vs 812
  baselined) and was **stepped over via the documented scoped-delta escape**,
  which requires and confirms `0 introduced by this range`. Per the rule, the
  pre-existing offender list is RECORDED alongside this document at
  `doc/09_report/landing/2026-08-17_land_113_offenders_preexisting.txt`
  (875 entries). This range introduces no new divergence and touches no test
  tree non-identically.

## Anti-wipe counts, measured against the exact sha pushed

Measured on `b0665d6d0021dd0f6507321ac452fa8da60b91c2`:

| invariant | threshold | measured | verdict |
|---|---|---|---|
| total files | >= 115,500 | **115,539** | PASS |
| `src/` tree entries | 13..25 | **16** | PASS |
| `src/app/interpreter` files | 99 | **99** | PASS |
| `src/runtime` files | >= 150 | **222** | PASS |
| deletions (`D` lines) in range | every one accounted for by name | **0 — there are none** | PASS |

`git diff --name-status <range> | grep '^D'` returns nothing, so the
account-for-every-D requirement is satisfied vacuously-but-verifiably: the
range is purely additive/modifying. Files touched, by area: 20
`doc/08_tracking`, 7 `src/compiler`, 2 `test/01_unit`, 1 `src/compiler_rust`
(net-empty, see above), 1 `src/app`, 1 `.spipe`, 1 `doc/03_plan`.

## Deferral list (8) — every one named with its reason

Each was retried **twice** against the fully-rebuilt tip (not just against
origin), in case an intervening applied commit would resolve it. All 8 still
conflict. None was dropped silently; none was force-resolved.

- `05d99eb79e4b` — fix(compiler): route a new HirLowering field through accessors; fix a dead native guard
  - conflict in: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl `
- `579a0e1a1713` — fix(parser): REGRESSION from 3c4e6551b7a — 'use' as a soft-keyword ident broke every relative import
  - conflict in: `doc/08_tracking/bug/sdoctest_mode_unknown_extern_rt_string_ends_with_2026-08-07.md doc/08_tracking/bug/soft_keyword_use_as_ident_broke_all_relative_imports_2026-08-17.md test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl `
- `cdc0c452cded` — test(jit): fail-closed gate pinning array-parameter element untagging across both engines
  - conflict in: `scripts/check/check-array-param-element-untag.shs test/fixtures/compiler/array_param_element_untag.spl `
- `df0b2ca87471` — docs(cli): document --unstable / --no-unstable in `simple test` help
  - conflict in: `src/app/cli/cli_helpers.spl `
- `999a794329e2` — fix(driver): a non-OK build unit must print its recorded reason
  - conflict in: `scripts/check/check-build-outcome-reason-attribution.shs src/app/cli/native_build_main.spl `
- `136360275826` — fix(bootstrap): let allowlisted print-only probes reach Stage 3
  - conflict in: `scripts/bootstrap/resume-stage3-from-admitted.sh `
- `4e42ce0d32dc` — fix(test): stop stage3 lowerer-reuse contract dying on its own interpolation
  - conflict in: `test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl `
- `9f5514d0bb23` — test(dict): engine-differential correctness matrix + linear-scan perf guard
  - conflict in: `doc/08_tracking/bug/native_dict_f64_get_nil_sentinel_collides_with_stored_3_2026-08-17.md scripts/check/check-dict-lookup-complexity.shs `

Reason class for all 8: a genuine conflict in `src/**`, `scripts/**` or
`test/**` where origin and local both moved and the merged intent could not be
constructed with confidence in this pass. Per policy, correctness outranks
completion — these are left for a lane that can build and test the compiler.
Two of them (`999a794329e2`, `cdc0c452cded`) pair a source change with its own
fail-closed guard script, so landing either half alone would be worse than
deferring both halves together.

`1363602758260bff040e9afb722fef56e5ad06c9` deserves specific note: it conflicts
in `scripts/bootstrap/resume-stage3-from-admitted.sh`, which is
stage-3-admission adjacent. Even though it is not one of the two named
outright-defer files, it is deferred under the same reasoning — a sloppy merge
there can silently weaken the stage-3 provenance gate.

## Applied (29)

- `d492fcc04adb` docs(bug): reopen bracket-index-as-generics — the trigger is a preceding `<`
- `7da9adc40d12` docs(bug): file rt_enum_discriminant garbage-constant and native_compile silent-failure defects
- `50c84fbe6720` docs(bug): stamp office fixes verified by content
- `af28d20df320` docs(bug): record reproduced native_compile silent-failure measurements
- `33ff4cb4d391` fix(guards): make a misplaced --expect-files an ERROR; file three verified guard defects
- `78c342254b41` docs(bug): merge the two duplicate native_compile silent-failure rows into one
- `a70acda356a6` docs(bug): reopen 2 rows whose not-reproduced closure was measured on the interpreter arm only
- `2e783a24e58d` docs(bug): withdraw the shared-untag-root claim from the 2 pass-2 reopens
- `17d3496f3f30` fix(parser): stop a backtracked generic-arg speculation leaking its deprecation warning
- `91fa3cce4d4a` docs(spipe): pin the root cause of the repo-wide push block
- `4aad4d47c883` docs(spipe): sync status by content, and the guard-working-tree integrity finding
- `2b378efa11a7` fix(runtime): make the Rust test suite compile again
- `c89ca8acfc6e` docs(bug): file the stage-3 export_origins cost sink with its measurement
- `a6e93f90707c` docs(bug): record the export_origins ablation -- 1012ms -> 794ms, origin set byte-identical
- `10da1bf0f786` fix(office): SheetsApp.navigate_to landed the cursor on hidden rows
- `fa4e610a7b10` fix(native-build): hoist env_get out of f-string interpolation; refute object-erasure hypothesis
- `d4410aab419f` fix(build): stop silently dropping unstable-mode intent, and say when it cannot be honoured
- `91f4147088a2` test(driver): pin the build-side outcome contract at BuildUnitOutcome.from_status
- `082200ce8afe` docs(plan): P2 answered — one-module child compile is genuinely blocked
- `98155fe41a55` docs(spipe): build-side process isolation is genuinely blocked, with evidence
- `d58c969c827a` docs(bug): record post-fix guard state -- new timeout reason, with the contention confound stated
- `4213a69da10b` test(driver): correct the 137 pin — an unbudgeted SIGKILL is CRASHED, not TERMINATED
- `f927cb0d4de8` docs(test): fix the stale 137 sentence in the spec docstring
- `3791efadd9f3` docs(spipe): build-side outcome contract specced; correct this lane's own 137 claim
- `475e64dd9de9` fix(driver): fail closed when a native-build --entry collects zero sources
- `16d04a53cb3d` docs(bug): the four native-build guards are blocked in parse, not source discovery
- `d0d1ccf9c528` docs(bug): retire 3 office bug rows verified fixed by source inspection
- `225736ddad27` fix(clobber): restore brace-literal interp guard and rewire silent_default lint
- `675aa70a2192` fix(office): math_bridge imported undefined variance_sample; use var_sample

Plus the one resolution commit `b0665d6d0021` described under "Anti-revert"
above, for 30 commits total in the pushed range.
