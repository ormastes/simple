# Phase 3 semantic pass counter discovery failure

Canonical attempt12 at release source `880e9464002aeb37fa4c6ae49312737e736fd48c`
finished all four Rust support builds and passed all five preflight checks.
Stage2 discovery then failed at `hir_body_semantic_lease_v1.spl:151:9`:
`Unexpected token: expected pattern, found Pass`.

The local counter used the reserved statement keyword `pass`. Rename only that
counter to `pass_idx`. The typecheck, safety, any-escape and enum-contract
ordering, warning/error publication and pass receipt names remain identical.

The original failure remains in external attempt12 evidence. The stage2 process
receipt records exit1, peak54864KiB, limit5859375KiB and quiescent1. No new Simple
compiler, Hello, CLI or runner was produced by this attempt.

This report records the concrete discovery bug; registry reconciliation remains
pending until a qualified bug database runner is available. Parser recheck and
fresh native qualification must be reported separately from the source repair.

Another lane landed the equivalent source repair as `4a21f1c6240209e99e8b8e01fa4a6a1d92ecd05c`
before this failure was observed. The next integration retains that exact
remote version rather than landing a second counter rename.
