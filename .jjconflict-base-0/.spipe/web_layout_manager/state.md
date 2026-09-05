# Web layout manager SPipe state

- Stage: interface-concrete
- Parent: `layout_framework`
- Selected scope: CPU-oracle adapter, deterministic dirty frontier, framework
  delegation, epoch-qualified mappings.
- Interface checkpoint: concrete contracts and entrypoints in
  `doc/03_plan/platform/structural_compute/web_layout_manager_plan.md`.
- Deferred: GPU kernels and renderer-session wiring until post-interface phases.
- Verification constraint: the deployed pure-Simple binary does not currently
  expose `check`, `test`, or `spipe-docgen`.
- Review: oracle and invalidation sidecars completed; concrete identity, profile
  admission, per-node dirty bits, resolved text metrics, hit regions, and checked
  epoch semantics are frozen.
- Static gates: conflict/stub/raw-runtime scan clean; working and staged
  direct-runtime guards pass.

