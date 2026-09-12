# macOS Stage4 lane: pre-existing test-tree divergence step-over

**Status:** OPEN (unverified 2026-09-12)

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
