# Web layout manager SPipe state

- Stage: design-interface
- Parent: `layout_framework`
- Selected scope: CPU-oracle adapter, deterministic dirty frontier, framework delegation, epoch-qualified mappings.
- Deferred: GPU kernels and renderer-session wiring until the interface checkpoint is pushed.
- Verification constraint: the deployed pure-Simple binary does not currently expose `check`, `test`, or `spipe-docgen`.
- Review: oracle and invalidation sidecars completed; concrete identity, profile admission, per-node dirty bits, resolved text metrics, hit regions, and checked epoch semantics are frozen.
- Static gates: conflict/stub/raw-runtime scan clean; working and staged direct-runtime guards pass.
