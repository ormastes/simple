# Pre-existing main gate debt blocking every PR (recorded offender list)

**Date:** 2026-08-31
**Status:** PARTIALLY RESOLVED — Offender 2 (repo hygiene) is CLEARED as of
2026-09-01; Offender 1 (guard wiring) remains OPEN.
**Recorded for:** the step-over required by `.claude/rules/vcs.md` — landing on a
scoped-delta pass REQUIRES recording the pre-existing offender list. An
unrecorded step-over is a violation even when the delta is clean. This is that
record.

**Applies to:** PR #147 (spipe slice 1) and PR #149 (search providers). Neither
introduces any offender below.

---

## Offender 1 — Guard-wiring ratchet: 1 orphaned guard

```
check-guard-wiring: FAIL — 1492 guard(s) checked, 1 NEW unwired
                    (745 baselined as known debt)
unwired_guard=check-context-pack-reduces.shs
```

**Not introduced by either PR.** Evidence:
- `scripts/check/check-context-pack-reduces.shs` already exists on `main`.
- PR #147 changed **0** files under `scripts/` or `.github/` — it is not
  possible for it to have unwired a guard.
- PR #149 likewise adds no guard and edits no workflow.

The guard's own message states the fix: wire it into `.github/workflows/` or
`scripts/hooks/`, or add it to `scripts/check/guard_wiring_optout.txt` **with a
reason**. It also says, correctly, "do not add an opt-out line merely to make
this pass" — so this record does NOT do that. Whoever landed the guard should
wire it.

## Offender 2 — Repo Hygiene: 86 forbidden-extension files

```
Violations: 86   (50 .sh, 17 .py, remainder other forbidden extensions)
FAILED: 86 violation(s) found
```

Representative offenders, all pre-existing, several at repo root:

```
./mod_doc.py                    ./soakrun.sh
./logs_launch2.sh               ./.w6gen.py
./.drv.sh                       ./.w6verify.sh
./valid/cluster.sh              ./valid/cluster2.sh
./sweep/classify.sh             ./tmpdrv/gen.sh
./evidence/run-attributable.sh  ./tools/claude-plugin/*/build.sh
./test/perf/webserver/live_h2load_compare.py
./test/perf/webserver/test_live_h2load_compare.py
./test/00_unit/scripts/fake-stage2-bootstrap.sh
./scripts/check/lib/bootstrap-stage3-provenance-verifier.sh
./scripts/release/converge-reviewed-fix.sh
```

**Zero of the 86 come from this session's work.** Verified by filtering the full
violation list for `spipe`, `common/search`, `.mjs` and `01_unit/app/spipe` —
no match. This session's files are `.spl`, `.md`, `.sdn`, `.json` and one
`.mjs`, none of which appear in the violation set.

These violate CLAUDE.md's "ALL code in `.spl`/`.shs`" rule and are real debt.
Fixing them means porting ~67 shell/Python files to `.spl`/`.shs` or recording
justified exemptions — a substantial piece of work, unrelated to search or the
knowledge compiler, and not something to smuggle into a feature PR.

---

## Why this record exists rather than a green build

Both gates are legitimately red and both legitimately block. The delta each PR
contributes is zero new offenders. `vcs.md`'s scoped-delta escape exists for
exactly this shape — a pre-existing red left by other work must not permanently
block landings that introduce no new divergence — but it is deliberately
mechanical, not a judgement call, and it requires this list to be written down
first so the debt cannot quietly accumulate unnoticed.

**What this record does NOT license:** it is not a general waiver. It covers
these two named gates, for these two PRs, on the evidence above. Any PR that
adds a forbidden-extension file or orphans a guard is still hard-blocked, and
"3 of 4 gates passed" remains not a licence for anything.

## Resolution of Offender 2 (2026-09-01)

`sh scripts/check/check-repo-hygiene.shs` now reports
`Violations: 0 / PASSED: repository is clean`.

Root cause: **all 91 violations trace to a single commit**, `e274cd33719`
("chore: merge all share-history worktree branches into main", 2026-08-27),
which both dumped session scratch into the tree and re-normalised CRLF files
to LF. Breakdown of the 91 and what was done:

| category | count | action |
|---|---|---|
| session scratch scripts committed by the merge (`.w6*`, `.w7*`, `.driver*`, `valid/`, `sweep/`, `tmpdrv/gen.sh`, `.audit/gap.py`, `run27.sh`, `soakrun.sh`, …) | 35 | deleted — every reference was intra-junk or a report doc |
| stale `.sh` duplicates the merge resurrected next to the live `.shs` (`scripts/release/{github-policy,converge-reviewed-fix,candidate-ref-create}.sh`) | 3 | deleted — every caller already invokes the `.shs` |
| real `.sh` files with in-repo callers | 3 | renamed `.sh` -> `.shs`, all callers updated |
| baselined files whose hash drifted by CRLF->LF only (`tools/claude-plugin/*/build.sh`, `tools/jupyter/*`) — reported twice each (new + stale row) | 17 x2 = 34 | baseline row re-fingerprinted in place, one `#` reason per row |
| baselined files with genuine forward changes (bootstrap resume/strategy fixes, riscv gate absolute-path removal) | 4 x2 = 8 | baseline row re-fingerprinted in place, reason cites the improving commit |
| `tools/claude-plugin/repo-and-pull-req/build.sh` — the merge REWOUND this validator, dropping `agents/review_loop_codex_first.md` and the L2 admission-contract sync check | 1 x2 = 2 | pre-merge logic restored (the referenced file still exists), re-emitted as LF, row re-fingerprinted |
| Python that must stay Python (cross-language `class_a.py` benchmark arm; live h2load/pgbench comparison harnesses and their pytest covers; pgwire interop probe) | 6 | baseline rows ADDED, one written reason each |

Nothing was bulk-regenerated: every baseline row carries an individual `#`
comment stating why. No file was deleted without first grepping its basename
for references. Baseline grew 40 -> 46 rows.

## Next step

1. Wire `check-context-pack-reduces.shs`, or opt it out with a stated reason.
   (`check-guard-wiring.shs` is still RED and is unchanged by the hygiene fix:
   byte-identical verdict before and after — `14 NEW unwired, 2 stale`.)
2. ~~Triage the hygiene violations~~ — DONE, see "Resolution of Offender 2".
3. Once guard wiring is green, this record should be closed and the escape
   retired.
4. Follow-up worth filing separately: `e274cd33719` was an unreviewed bulk
   worktree merge that both committed scratch and rewound at least one file
   (`repo-and-pull-req/build.sh`). Other, non-hygiene-visible rewinds from that
   commit have NOT been audited.
