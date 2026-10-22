# Producing both planner receipts in one Stage 2 run invalidates the Stage 3 one

- Status: OPEN
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Blocks: `--resume-stage3-from-admitted` after a Stage 2 run that passed both
  `--produce-stage3-receipt=<reason>` and `--produce-managed-receipt=<reason>`.

## Observation

`bootstrap-from-scratch.sh` (around :4590-4625) runs
`produce-bootstrap-planner-admission-v2.shs` twice against the same admitted
parent: first for `//bootstrap:stage3`, then for `//bootstrap:stage4`. Both
write the planner executable to the same path,
`<output>/admission/<parent-digest>/planner`. The planner build is not
byte-reproducible (three builds of the same source gave sha256 `330da5d7...`,
`3cbe78e0...`, `596a901e...`), so the second write replaces the binary the
first receipt is bound to. The resume then refuses the Stage 3 receipt:

```text
bootstrap-policy-error: planner-admission-v2-unbound
bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2
```

`bootstrap_planner_v2_verify_bound` re-hashes `planner` (3cbe78e0..., the
Stage 4 build) against the Stage 3 receipt's `planner_sha256` (330da5d7...).

## Recovery used

Re-running the canonical producer for `//bootstrap:stage3` alone against the
same parent (`--parent-compiler=<output>/stage2/<triple>/simple`) produced a
receipt that verifies; that in turn invalidates the Stage 4 receipt.

## Fix direction

Give each target its own admission directory (or make the planner build
reproducible and refuse to overwrite a differing binary).
