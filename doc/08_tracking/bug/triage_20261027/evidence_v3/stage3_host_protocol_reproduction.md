# Scoped reproduction evidence: Stage 3 source policy

**Bug:** [`BUG-STAGE3-RESUME-SOURCE-POLICY-20261011`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_resume_source_policy_2026-10-11.md)  
**Assessment:** `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`  
**Mandatory scope:** `HOST_PROTOCOL` only, case `test_real_digest_and_worker_builders_match`.

This is one host-side shell argument-builder reproduction. It does not reproduce an actual compiler build, qualify the Simple runtime, or establish a full Phase 3 result.

## Retained red and post-target green

| Receipt | Exact command | Exit | What it establishes |
|---|---|---:|---|
| `exec-f1426a88-b544-492a-9bb1-3e213ab7524f` | `/bin/bash -lc 'python3 scripts/bootstrap/tests/stage3-source-policy-test.py'` | 1 | Baseline at `b0d3cf73dc19e75640952c220bf0e069230b5eda`; six host protocol tests ran. The admitted failure is actual/digested source-policy argv mismatch. |
| `exec-12af553a-00fe-44f9-b64c-a872d0e83352` | `/bin/bash -lc 'python3 scripts/bootstrap/tests/stage3-source-policy-test.py'` | 0 | Same host suite after remedy edits and before creation of commit `28493de7580915b9fc0fd104cd55cea9bb07edc5`; the later commit records the matching code state. This is post-target only, not evidence that frozen `c0` is fixed. |

The red command was the next retained command after the owned baseline worktree was created at history ordinal 115; it ran before edits at ordinal 122. The retained review read the command history SQLite database read-only (thread `01a17be0-e526-7de1-9fc3-cc90bf83a25d`). No test, build, or compiler command was rerun for this checkpoint.

The six-test red suite reported three failures. Only the source-policy vector mismatch below is admitted for this bug; typed-prefix index and obsolete argument-count failures are not separately admitted as product reproductions.

**Reviewer-report paraphrase of the retained receipt, not verbatim output:** In `test_real_digest_and_worker_builders_match`, the digest vector included ordered `--source` roots and `--entry-closure`, while the worker vector ended at `src/app/cli/bootstrap_main.spl`.

The digest contained six ordered source pairs plus `--entry-closure`; the worker command omitted the policy tail. The green receipt was recorded before creation of commit `28493de7580915b9fc0fd104cd55cea9bb07edc5`; that commit records the matching remedy code. The receipt is post-target and host-protocol-only, and does not convert the historical `c0` defect to a fix.

## Source binding across the target boundary

The executed baseline was `b0d3cf73dc19e75640952c220bf0e069230b5eda`; the reviewed target is `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`. The retained independent review compared 14 test/producer/worker/helper blobs and found every listed blob identical at both commits. This binds the host-protocol result to the assessed dependency set only, not to whole-tree equivalence:

| Dependency at frozen target | Blob at baseline and target |
|---|---|
| [`scripts/bootstrap/tests/stage3-source-policy-test.py`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/tests/stage3-source-policy-test.py) | `07919733f9f9c7c7fb5fa1fb1a0d16f7d7065335` |
| [`scripts/bootstrap/tests/stage3-worker-lowering-lane-test.py`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/tests/stage3-worker-lowering-lane-test.py) | `f91e0b0e82c4e9942a35c036539870bfccf3aa25` |
| [`scripts/bootstrap/tests/stage3-worker-lowering-lane-p-f-test.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/tests/stage3-worker-lowering-lane-p-f-test.shs) | `721d5adcac4ad2810bfa899ce8b13c7612522745` |
| [`scripts/bootstrap/lib/stage3-native-build-worker.sh`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/stage3-native-build-worker.sh) | `061bcd067af864b83aac36505f152d0e801b4f14` |
| [`scripts/bootstrap/lib/stage3-source-policy.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/stage3-source-policy.shs) | `a37c9c3458cbd368f6779d55173e702d025ab79d` |
| [`scripts/bootstrap/resume-stage3-from-admitted.sh`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/resume-stage3-from-admitted.sh) | `5989f9926f8c5a474f49235cfbd31285d486d565` |
| [`scripts/check/lib/bootstrap-stage3/authority.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/lib/bootstrap-stage3/authority.shs) | `ee34c9ac3c63753592dcfad9b3e48a830c5d5d02` |
| [`scripts/check/lib/bootstrap-stage3/command-snapshot.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/lib/bootstrap-stage3/command-snapshot.shs) | `707ec0d0e977915026698f8e522b885c0ab0e450` |
| [`scripts/bootstrap/lib/tree-rss-policy.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/tree-rss-policy.shs) | `275e1f929da3ed904bf35a882ed615cb45336617` |
| [`scripts/resource/process-tree-rss-watchdog.pl`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/resource/process-tree-rss-watchdog.pl) | `1a3ca4f67ef3bb62656fd63fe59834ae6ff88a07` |
| [`scripts/check/bootstrap_compiler_ceiling_transport_test.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/bootstrap_compiler_ceiling_transport_test.shs) | `58e7116a2268b32cfd7d23f3d83aeedeef7e6391` |
| [`scripts/check/check-stage3-rss-policy-transfer.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-stage3-rss-policy-transfer.shs) | `2bb5d3f71488788f61d1e5bbffc464a59c86548b` |
| [`test/01_unit/scripts/bootstrap_cache_hir_controls_test.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/scripts/bootstrap_cache_hir_controls_test.shs) | `2c36af6caa1565d5e4fcaa8726bcc5a67d2a5961` |
| [`test/01_unit/scripts/bootstrap_stage3_abi_forwarding_test.shs`](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/scripts/bootstrap_stage3_abi_forwarding_test.shs) | `1476eb7065aef14d47351e00865cc15ad2112a9c` |

See the production [source policy helper](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/stage3-source-policy.shs), [resume wrapper](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/resume-stage3-from-admitted.sh), and [native build worker](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/stage3-native-build-worker.sh) for the reviewed production boundary. The observed contract is that digest construction uses the authenticated ordered source vector and closure flag, while the worker launch omitted those arguments at the frozen target.

## Explicit qualification limits

- Full Phase 3: `UNRUN`.
- Compiler build: `UNRUN`.
- Normal CLI qualification: `UNRUN`.
- Simple runtime qualification: `NOT_QUALIFIED`.
- This evidence is not a compiler build reproduction and does not establish full Phase 3 success.
- The separate green receipt is after the target and is informational only.

The retained source receipt used read-only history and exact dependency identities. Its evidence files are hashed in [`manifest_v3.sdn`](../manifest_v3.sdn); no temporary-only evidence path is needed to interpret this page.
