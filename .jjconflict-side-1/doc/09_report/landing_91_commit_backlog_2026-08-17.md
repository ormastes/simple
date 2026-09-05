# Landing record — 91-commit backlog rebased and pushed, 2026-08-17

**Pushed sha: `810018b7a114787a45e04444bfee55b34fe830b1`**

Proof (not an exit code — a clean exit has lied on this remote before):

```
$ git ls-remote origin main
810018b7a114787a45e04444bfee55b34fe830b1	refs/heads/main
```

Push was `git push --no-verify` (`--no-verify` explicitly user-authorised: "push
no verify"). **Never `--force`.** One non-fast-forward rejection occurred and was
handled by re-fetch + rebase + retry, never by forcing.

## Range

The local backlog was rebased **three times**, because origin moved twice while
work was in flight. Each base is recorded because the guard verdicts below are
attributable only to the base they were measured against.

| pass | base (origin/main at the time) | commits attempted | landed | dropped as already-upstream |
|---|---|---|---|---|
| 1 | `f2531d57bdf` | 91 | 48 | 43 |
| 2 | `0f5b67b79b4` | 48 | 14 | 34 |
| 3 | `1983ecdbce9` | 14 | **13** | 1 |

Final pushed range: **`1983ecdbce9..810018b7a11`, 13 commits.**

**Total dropped as already-upstream across the three passes: 78 of 91.** This is
the expected shape, not a loss — a parallel lane was landing an overlapping
subset of the same backlog throughout, and an earlier independent audit of an
overlapping range found 41 of 68 already landed by content.

### Verification that the drops are genuine, by CONTENT not by sha or subject

- **32 dropped by exact patch-id equality**: `git cherry f2531d57bdf 4e42ce0d32d`
  reported `32 -` / `59 +`.
- **Remaining drops went empty when applied**, which git reports as
  "skipped previously applied commit" or an empty pick.
- **Sample spot-checks by content** (a subject or a sha proves nothing — a commit
  was announced as a fix today whose tree was byte-identical to its parent):
  - `fix(test-runner): stop counting externally-killed specs as failures`
    (`530fa623afa`) — `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`
    **byte-identical** at origin (`git rev-parse` of both blobs equal).
  - `fix(guards): the Metal NTT gate made the pre-push hook unpassable`
    (`047256836733`) — `scripts/check/check-x25519mlkem768-metal-ntt.shs`
    **byte-identical** at origin.
  - `fix(parser): REGRESSION from 3c4e6551b7a` (`579a0e1a171`) — not identical,
    so checked directionally: `git diff 579a0e1a171 HEAD --
    src/compiler_rust/parser/src/expressions/postfix.rs` yields **only `+`
    lines**. Origin is a strict superset; nothing was rewound.
- **Whole-tree cross-check across pass 1 → pass 2**: only **8 files** differed
  between the pass-1 tip tree and the pass-2 tip tree, i.e. origin had absorbed
  the rest verbatim. No content vanished in the drop count.

### The 13 commits pushed

```
810018b7a11 fix(test): stop stage3 lowerer-reuse contract dying on its own interpolation
756c8a9678e docs(bug): record the resolving SHA for the Calc cursor hidden-row row
68596e901bd fix(office): SheetsApp.navigate_to landed the cursor on hidden rows
61b3a2bd35d docs(bug): correct the int61 row's false VERIFIED FIXED header
93fcfde2dc8 fix(guard): gate seed-build check on test targets too; file the three blind spots
ff28dcb98e5 docs(bug): record the export_origins ablation -- 1012ms -> 794ms, origin set byte-identical
fac64a00d86 fix(seed): declare required-features=llvm on the two M4 probe examples
69d0d2e8479 feat(office): fill series (autofill) for spreadsheet ranges
5d292b6a9c1 docs(bug): file the stage-3 export_origins cost sink with its measurement
a01f9458bdc fix(lib): add diverging else: to four refutable val bindings; file two parser continuation bugs
592dc163aa6 docs(bug): close 6 self-contradicting OPEN records verified fixed by source
3da492c01e0 fix(guards): verdict contracts for the gpu and bootstrap guards; os/runtime triage
f2e527b68a6 chore(office): remove 8 tracked backup/tmp artifacts
```

## Conflict resolutions

Work was done in an **isolated `git worktree add --detach`**, never in the shared
tree (which holds several lanes' uncommitted edits under `src/compiler_rust`).
`git config core.bare` on the shared repo was checked after the `worktree add`
and read `false` — the failure mode described in the rules did not occur.

**No `-X ours` / `-X theirs` was used anywhere.** Both the `-` and `+` sides were
read on every conflict. No commit was `rebase --skip`ped for a conflict; the only
skips were commits git itself reported as empty.

### Non-doc resolutions, each with its reason

**1. `scripts/bootstrap/resume-stage3-from-admitted.sh`** (commit `13636027582`,
"let allowlisted print-only probes reach Stage 3") — **kept origin wholesale.**

This was flagged as the single highest-risk file in the range because it computes
the stage-3 admission args-hash, and a sloppy merge there silently weakens a
provenance gate. Measured, not inferred:

- Origin already carries this commit's actual payload: `grep -c
  'stage3_diagnostic_env'` on `f2531d57bdf:scripts/bootstrap/resume-stage3-from-admitted.sh`
  → **4**, and `bootstrap_stage3_diagnostic_env` is present in
  `f2531d57bdf:scripts/check/lib/bootstrap-stage3/authority.shs`.
- The residual conflict was origin's **later** evolution, not our fix: origin
  derives the backend from the stage-2 transcript
  (`stage2_backend=$(bootstrap_stage3_transcript_argv_value_after "$stage2_transcript" --backend)`),
  **validates it against an allowlist** (`case "$stage2_backend" in
  llvm|llvm-lib|cranelift) ;; *) exit 1 ;; esac`), and uses
  `--backend "$stage2_backend"` at both call sites. `grep -c 'backend cranelift'`
  at origin → **0**.
- Our side would have **rewound** that to a hardcoded `--backend cranelift` at
  both sites.
- **Correction to an earlier reading of mine, stated here so the record is
  right:** origin did **not** delete the args-hash computation.
  `grep -c 'args_sha256\|stage2_args'` at origin → **4**. The choice was never
  "has a hash" vs "no hash"; it was a transcript-derived, allowlist-validated
  backend vs a hardcoded one. That makes keeping origin more clearly correct, not
  less.

The two paths named as owned by a concurrent reconciling lane —
`scripts/bootstrap/bootstrap-from-scratch.sh` and
`scripts/check/lib/bootstrap-stage3/authority.shs` — are **not in the pushed
range at all**, because that bootstrap commit went empty. Measured:
`git diff-tree -r --name-only <base>..<tip> -- <those two paths>` returns
**empty**.

**2. `scripts/check/check-build-outcome-reason-attribution.shs`** — kept origin's
superset: `SIMPLE="${SIMPLE_BINARY:-${SIMPLE_BIN:-$REPO_ROOT/bin/simple}}"`. Ours
had the plain `SIMPLE="$REPO_ROOT/bin/simple"` and would have **removed an
injection point another lane added deliberately** so a fresh worktree can supply
a compiler instead of silently passing without one.

**3. `test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl`** —
kept origin's anchor. Both lanes fixed the same defect (a literal `{source_idx}`
in the spec's own string being interpolated); origin escaped it by concatenating
around the brace, ours truncated the anchor. Origin's is the more precise of two
equivalent fixes and was already upstream. Our commit's explanatory comment
merged cleanly, so its now-stale last sentence was reworded to describe the
concat escape rather than the truncation — otherwise the record in the file would
have been false.

**4. `src/app/cli/cli_helpers.spl`** (commit `dbae6fcd5d7`) — kept origin. Origin
already documents `--unstable` / `--no-unstable` with **identical semantics**
(the `OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN` classification, TERMINATED and
TIMEOUT as unverified rather than failures, ON for bootstrap and OFF for
interactive). Only the line-wrapping of the help text differed.

### Doc and state resolutions — both sides kept

Conflicts under `doc/08_tracking/bug/` and `.spipe/` were resolved by **union**
(marker lines removed, both sides' content retained), which is the right default
for bug rows where one lane's REOPENED sits alongside another's MECHANISM
LOCALISED. Files: `interp_array_param_indexing_2026-07-03.md` (×3),
`rt_dir_list_platform_header_collides_with_extern_2026-08-10.md`,
`stage3_export_origins_linear_module_lookup_2026-08-17.md` (×2),
`native_compile_fails_with_no_diagnostic_stderr_truncated_from_middle_2026-08-17.md`,
`parser_block_if_expr_trailing_inline_else_2026-08-17.md` (×2),
`.spipe/unstable_test_mode/state.md` (×6).

One of these was resolved by `rerere` replaying an earlier resolution rather than
by hand, so it was audited afterwards rather than trusted:
`comm -23` of each side's sorted unique lines against the resolution returned
**empty in both directions** for
`rt_dir_list_platform_header_collides_with_extern_2026-08-10.md` — no line from
either side was lost.

## Anti-revert

Every changed source file was checked as a forward delta, not a rewind. This is
not theoretical: a commit today titled "fix(test): matrix spec died at load"
(`9e65c5356b65`) was a stale-snapshot clobber that deleted 79 files two minutes
after they landed.

- `src/compiler_rust/runtime/src/value/core.rs` — **purely additive**
  (`INLINE_INT_BITS`, `fits_inline_int`, plus doc comments). `from_int` is
  untouched; the int61 lane's work is intact.
- `src/compiler_rust/parser/src/expressions/postfix.rs` — tip is a **strict
  superset** of the dropped `fix(parser)` commit (diff against it yields only
  `+` lines).
- Frozen contract strings, origin → tip, **non-decreasing**: `CRASHED:` 18 → 19,
  `TERMINATED:` 469 → 471. `print_help` / `print_version` still defined in the
  same 5 and 2 locations respectively (the `-` lines in `help.rs` were
  reformatting inside the same file, not a removal).
- All large deletions in the range are the accounted file removals below; no
  reverted function body was found.

## Anti-wipe, measured against the exact pushed sha `810018b7a11`

`main` was wiped to near-zero files twice in 24 hours with every text-and-tree
guard green. Counting files is the only thing that ever caught it.

| check | measured | expectation |
|---|---|---|
| `git ls-tree -r --name-only 810018b7a11 \| wc -l` | **115,511** | ≥ ~115,400 ✓ |
| `... -- src/app/interpreter \| wc -l` | **99** | 99 ✓ |
| `git ls-tree --name-only 810018b7a11 -- src/ \| wc -l` | **16** | band 13..25 ✓ |
| `... -- src/runtime \| wc -l` | **222** | ≥ 150 ✓ |
| conflict-marker text in tracked non-vendored files | **0** | 0 ✓ |

`git diff-tree -r --name-status 1983ecdbce9..810018b7a11` shows **9 `D` lines,
every one accounted for by name**:

- **8 tracked backup/tmp artifacts** removed by `f2e527b68a6`
  (`chore(office): remove 8 tracked backup/tmp artifacts`):
  `src/app/office/erp_bridge.spl.pre-erp`,
  `file_formats.spl.pre-comments`, `mod.spl.pre-erp`,
  `odf_ooxml.spl.pre-comments`, `odf_ooxml.spl.pre-styles`,
  `office_api.spl.pre-erp`,
  `slides/deck_format.spl.tmp.3421194.9f60920de537`,
  `word/html_render.spl.pre-comments`.
- **1 duplicate consolidation**: `src/app/debug/remote/types.spl` (189 lines),
  deleted by `592dc163aa6` with its importers repointed from
  `app.debug.remote.types` to `std.nogc_sync_mut.debug.remote.types`. The target
  was verified present at the pushed tip
  (`src/lib/nogc_sync_mut/debug/remote/types.spl`).

A 10th deletion present in earlier passes,
`src/app/dap/adapter/trace32.spl` (a byte-identical unimported duplicate removed
by `fix(dap)`), dropped out of the final range because origin landed it first.

## Guards

**Binary identity, stamped because it is not stable.** All binary-dependent
verdicts below are attributable **only** to this identity:

```
bin/release/x86_64-unknown-linux-gnu/simple
size  59537240
mtime 2026-08-17 12:58:51 UTC
still the Rust seed ("this Rust-built Simple binary is a bootstrap seed only")
```

The deployed binary **changed twice within four minutes** today (59536728 at
22:59:37 the previous day → 59617400 at 12:54:48 → 59537240 at 12:58:51), the
intermediate 59617400 build was **not preserved**, and the third replacement is
unattributed. Only the original stale binary survives as
`simple.pre-redeploy-20260817T125448Z` (59536728). Nothing was rebuilt or
redeployed by this lane; the deployed binary was symlinked into the worktree,
since `bin/` is gitignored and a fresh worktree has none.

### Obtained verdicts — verbatim, measured against base `f2531d57bdf` (pass 1)

```
check-no-conflict-tree-push: PASS — 48 commit(s) checked in f2531d57bdf..HEAD, 0 conflict trees (repo .../scratchpad/land-wt)
check-no-conflict-markers-push: PASS — 137 file(s) scanned at 6e301f978b5b8a647bed3800c78da521065be808 across 48 commit(s) in f2531d57bdf..HEAD, 0 conflict markers (repo .../scratchpad/land-wt)
check-tree-size-push: PASS — 48 commit(s) checked in f2531d57bdf..HEAD, each banded against its own first parent, range base 115484 file(s) (measured at base f2531d57bdf), 0 structural faults (repo .../scratchpad/land-wt)
check-runtime-api-regression-push: PASS — 2795 symbol(s) checked, 0 removed
```

**These four were measured on the pass-1 tip `6e301f978b5b`, not on the pushed
`810018b7a11`.** The pushed tip is a subset of that content rebased onto two
later origins (only 8 files differed between the pass-1 and pass-2 tip trees), so
they are strong evidence but they are **not** verdicts on the pushed sha, and
this record does not claim they are.

### Unobtained verdicts — recorded as UNOBTAINED, not as passes

```
check-seed-builds-push: ERROR — killed by SIGTERM (143) — a harness timeout, earlyoom, or an explicit kill. Re-run detached (setsid) with no cap.
check-seed-builds-push: ERROR — nothing was checked (exit 2)
```

That SIGTERM was **my own `TaskStop`**, issued to free the worktree for the
re-rebase after the user said "push no verify". Per the rules, rc=143 is
UNVERIFIED — it is neither a pass nor a failure, and it is recorded here as
neither.

Three more were never reached and are **UNOBTAINED**:

- `check-test-tree-divergence.shs` — not run. Known **pre-existing RED**
  (876 vs 813) independent of this range.
- `check-c-runtime-compiles-push.shs` — not run.
- `check-seed-builds-push.shs` — see the SIGTERM above; no verdict.

**Nothing in this section may be read as a pass.** Four verdicts were obtained on
a near-identical earlier tip; three were not obtained at all.

## What was stepped over, and why

- **`--no-verify` on the push**, explicitly user-authorised ("push no verify").
  This is what let the push proceed without the four unobtained guard verdicts
  above. What stands in their place is not nothing: the anti-wipe counts were
  measured against the exact pushed sha, the anti-revert review was done hunk by
  hunk on every source path, and four guards passed on a tip differing from the
  pushed one by 8 files.
- **`check-test-tree-divergence` pre-existing RED** was not resolved and its
  scoped-delta escape was **not used** — the guard was not run at all in either
  mode, so there is no delta-PASS and no offender list to record. Stated plainly
  rather than implied: this range's effect on test-tree divergence is
  **unverified**.
- The 392 accumulated stale worktrees in the shared repo were left alone, as
  instructed — other lanes hold live ones.
- `/mnt/data/worktrees/simple-boot-snap` was not touched.
- `bin/simple` and `bin/release/**` were not rebuilt or redeployed.
