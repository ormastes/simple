# RC1 macOS Stage 2 positional frontend smoke times out

**Status:** Open. The RC1 Stage 2 compiler links, but bootstrap admission fails.
**Candidate source:** `141711525226a29e498262d37da1b92ada90c06b` on the stacked RC1 fixes.
**Platform:** `aarch64-apple-darwin`, LLVM 18, `--full-bootstrap --stop-after-stage2`.

## Retained evidence

The third bootstrap attempt built a Stage 2 binary (`3 compiled, 767 cached, 0 failed`) and reached compiler sanity. The prior Mach-O runtime-owner rejection did not recur. The sanity receipt reports `status=fail`, `frontend_smoke_status=1`, and `frontend_smoke_bootstrap_mode_status=0`; its candidate SHA-256 is `ba9d59ee142e44408ab2eb58d0f7b6a43325a8be1035b182cb8de61ed9e9da3c`. The preserved frontend log contains:

> candidate_frontend_smoke: candidate HUNG (timeout) native-building a two-line hello world with a positional entry

This is the first smoke pass (`SIMPLE_BOOTSTRAP=0`); the second pass was not reached. The admission helper deleted its probe directory, including `build.log`, so the timeout phase cannot be reconstructed from that run. The full frontend log is retained at `build/bootstrap/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log` in the isolated admission worktree.

Standalone invocations of the rejected binary against the same source revision did not reproduce the timeout: a mode-0 invocation returned an MC/DC budget configuration error, while a mode-1 invocation reached MIR and returned `E-SFFI-016: missing return in non-unit function 'main'`. Those invocations did not reproduce every inherited environment variable of the bootstrap wrapper and do not establish the timeout's cause.

## Next diagnostic boundary

Commit `4554484a116` makes the RC1 helper append at most the last 4,096 bytes of the positional build log to its failure output before deleting the probe directory. The outer sanity function now retains that output beside its receipt. On a later permitted admission run, compare the captured phase and exact inherited environment with a standalone reproduction; keep the timeout and clean failure distinct. The three full bootstrap verify/fix cycles for this session are exhausted, so this log-capture change has not received another full admission run.

Bootstrap remains unadmitted. Neither the linked binary nor the focused codec regression is evidence of a successful macOS bootstrap.
