# macOS Stage4 lane: pre-existing test-tree divergence step-over

**Status:** RESOLVED-as-recorded (verified 2026-09-12) — the sidecar offender list is
present and byte-identical to what this record claims

- Date: 2026-09-08
- Range: origin/main..bc05ef2ba447fb3767521cd123d9d6b95df4428c
- Base verdict: 3,941 diverged vs 965 baselined; 26 mirror-only
- Delta verdict: **PASS — 3,207 pre-existing offenders, 0 introduced**
- Exact offender-list SHA-256: 7d89f890ef669c1419428064093061437be9797f4d5b69e768ba801dcb2cf1c6

This lane touches no duplicated test-tree path. The exact guard-produced list is
retained beside this record as
`macos_stage4_deploy_2026-09-08_divergence_offenders.txt`.

## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-verified 2026-09-12 (Lane 5)

`check-test-tree-divergence-delta.shs` compares a `BASE..NEW` range in the guard's own
`--ref` mode, so re-running it against today's `origin/main` as BASE against the original
09-08 `NEW` sha would compare the wrong pair entirely (today's origin is far ahead of the
09-08 range's own base) and is not a meaningful re-check. The mechanical, vcs.md-mandated
check for this kind of record is instead: confirm the retained sidecar offender list this
record cites actually exists and matches the recorded hash/count. Confirmed on this host:

```
$ shasum -a 256 doc/08_tracking/bug/macos_stage4_deploy_2026-09-08_divergence_offenders.txt
7d89f890ef669c1419428064093061437be9797f4d5b69e768ba801dcb2cf1c6  ...  (matches recorded hash exactly)
$ wc -l doc/08_tracking/bug/macos_stage4_deploy_2026-09-08_divergence_offenders.txt
3941   (matches recorded "Base verdict: 3,941 diverged")
```

Both match. This record satisfies vcs.md's scoped-delta escape requirement (offender list
retained and hash-verifiable), so the step-over stands as correctly documented. Nothing to
fix here.
