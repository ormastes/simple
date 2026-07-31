# Web layout manager SPipe state

- Stage: verify-static-warn
- Parent: `layout_framework`
- Selected scope: CPU-oracle adapter, deterministic dirty frontier, framework delegation, epoch-qualified mappings.
- Deferred: GPU kernels and renderer-session wiring until the interface checkpoint is pushed.
- Verification constraint: the deployed pure-Simple binary does not currently expose `check`, `test`, or `spipe-docgen`.
- Review: oracle and invalidation sidecars completed; concrete identity, profile admission, per-node dirty bits, resolved text metrics, hit regions, and checked epoch semantics are frozen.
- Static gates: conflict/stub/raw-runtime scan clean; working and staged direct-runtime guards pass.
- Implementation: CPU-oracle adapter, exact invalidation frontier, framework delegation, checked epochs, and generation-qualified hit regions complete.
- Evidence: unit and system specs plus manual companions written; canonical pure-Simple binary still reports `unknown command 'check'` and cannot execute them.
