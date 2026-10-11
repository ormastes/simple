# Resource pinning lifetime regression manual

Executable: `test/01_unit/compiler/resource/resource_pinning_lifetime_spec.spl`.

The six hand-built MIR scenarios assert:

- A synchronous reference call completes before owner release: zero errors.
- Owner release precedes a later direct-reference call: at least one error.
- Owner release precedes a later copied-reference call: at least one error.
- A copied-reference call completes before owner release: zero errors.
- Owner release precedes a later moved-reference call: at least one error.
- A value-returning call may return an alias: retain the borrow conservatively.

The separate original pending-reference pinning assertion is unchanged.
Diagnostics are cached-bootstrap observations only; see the tracking note for
exact source bindings, receipts, and OPEN CFG/retention/admitted-runtime gates.
