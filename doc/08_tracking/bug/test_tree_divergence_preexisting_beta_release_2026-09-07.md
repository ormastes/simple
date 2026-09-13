# Pre-existing test-tree divergence stepped over on the 1.0.1-beta.1 landing

**Status:** OPEN (unverified 2026-09-12)

Range: `origin/main..65817763e31` (the `1.0.1-beta.1` version-projection cut).
Recorded per the scoped-delta escape in `.claude/rules/vcs.md`, which requires
the pre-existing offender list to be written down before landing on a
delta-PASS.

Delta verdict (`scripts/check/check-test-tree-divergence-delta.shs origin/main 65817763e31`):

```
PASS — 3210 pre-existing offender(s), 0 introduced by this range
```

Base verdict at `origin/main`, for context — this is the red this landing steps
over, and it is not this change's debt:

```
FAIL — 3944 diverged vs 965 baselined (3082 new, 103 fixed-but-still-baselined);
26 mirror-only (25 unallowlisted, 0 stale-allowlist)
```

The range touches no file under `test/`; it changes 17 version projections, one
CHANGELOG entry, and two tracking records. Zero new divergence is therefore the
expected result rather than a lucky one.

Full offender list: `test_tree_divergence_preexisting_beta_release_2026-09-07.txt`
(3944 lines, sha256 `350e5bef70fd1202c5acfc7dd88a6479375b1a482e20e82ea9075c61cd3ed00d`).

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
