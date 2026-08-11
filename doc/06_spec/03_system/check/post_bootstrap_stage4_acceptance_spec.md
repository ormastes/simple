# Post-bootstrap Stage 4 acceptance

## Purpose

Admit one exact source-bound pure-Simple Stage 4 candidate after bootstrap,
without rebuilding or rerunning retained smoke.

## Preconditions

- Absolute `STAGE4_POST_BOOTSTRAP_BINARY` under `build/bootstrap/full/<triple>`.
- Adjacent absolute `STAGE4_POST_BOOTSTRAP_PROVENANCE` receipt.
- Retained build and smoke logs matching their recorded hashes.

## Scenarios

1. Missing inputs are rejected.
2. Symlink candidate substitution is rejected.
3. Exact content and lineage are admitted with unchanged smoke evidence.

## Command

```bash
STAGE4_POST_BOOTSTRAP_BINARY=/absolute/path/to/build/bootstrap/full/<triple>/simple \
STAGE4_POST_BOOTSTRAP_PROVENANCE=/absolute/path/to/build/bootstrap/full/<triple>/simple.provenance.env \
$STAGE4_POST_BOOTSTRAP_BINARY test test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl \
  --mode=interpreter --no-session-daemon --sequential --no-db --no-cache --assert-ran --fail-fast
```

PASS proves current content and lineage, not a unique wall-clock build event,
deployment, rollback, QEMU, external native hosts, or physical Uno-Q.
