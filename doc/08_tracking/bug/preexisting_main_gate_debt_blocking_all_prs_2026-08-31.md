# Pre-existing main gate debt blocking every PR (recorded offender list)

**Date:** 2026-08-31
**Status:** OPEN — main's debt, not any one PR's
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

## Next step

1. Wire `check-context-pack-reduces.shs`, or opt it out with a stated reason.
2. Triage the 86 hygiene violations: port, or record justified exemptions.
3. Once both are green, this record should be closed and the escape retired.
