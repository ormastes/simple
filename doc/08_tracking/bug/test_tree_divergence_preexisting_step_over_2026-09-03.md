# Pre-existing test-tree divergence stepped over by chore/repo-cleanup-2026-09-03

**Date:** 2026-09-03
**Status:** RECORD ONLY — no divergence introduced, none fixed
**Rule:** `.claude/rules/vcs.md` § "Scoped-delta escape" requires the pre-existing
offender list to be recorded in the commit message or a `doc/08_tracking/bug/`
record before landing on a delta-PASS. This is that record.

## Measurements (2026-09-03, base `origin/main` e22cc20e40a)

`sh scripts/check/check-test-tree-divergence.shs --ref <NEW>` — the mode the
guard runs in — is RED on `origin/main` itself, independent of this branch:

```
check-test-tree-divergence: FAIL — 3955 diverged vs 965 baselined
  (3085 new, 95 fixed-but-still-baselined); 26 mirror-only
  (25 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
```

The sanctioned scoped-delta check, run in `--ref` mode on BOTH sides as the rule
requires (never the working copy):

```
sh scripts/check/check-test-tree-divergence-delta.shs e22cc20e40a <NEW>
check-test-tree-divergence-delta: PASS — 3205 pre-existing offender(s),
                                  0 introduced by this range
```

## Offender list

3955 lines, `sha256 3e2247fad468a0c89edff5faa84caa81c964df27ca00ae2e3301c855d9a7709a`,
emitted by the delta helper itself. Not committed: it is a 3955-line generated
census of a pre-existing condition, and `doc/09_report/` is temporal — the sha
above pins exactly which list was seen, and the helper regenerates it verbatim
from the same two revisions.

## Why this range touches the test trees at all

The root purge removes `test/01_unit/compiler/i18n/extractor_isolated/target/**`
(cargo llvm-cov build output, 30MB) and `tools/tls_test_server/target/**`. Those
are build artefacts under a test path, not spec files, which is why the delta is
zero despite the range touching `test/`.

## Not claimed

This record does not claim the divergence is harmless, and does not shrink it.
`check-test-tree-divergence` is NOT one of the 12 `push,` rows of
`config/check/must_check_gates.sdn`, so it does not gate a push today — that gap
is itself worth its own record and is not addressed here.
