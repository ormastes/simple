# SCV Workspace Restore Mutation Owner Blocker

**Disposition:** blocked; design and future BDD plan only. Native/runtime
verification is **NOT_RUN**.

The current restore path can write and remove workspace paths sequentially,
but no shared descriptor-rooted native owner exposes the operations required
to make those changes safe against leaf replacement and recoverable across a
crash. Existing path identity checks and advisory locks do not close the
check-then-mutate race. The hosted safe-artifact provider cannot be reused as a
workspace owner because it assumes private publication parents and does not
provide workspace quarantine semantics.

**Required fix:** admit a shared retained-root mutation provider with
descriptor-relative no-follow resolution, atomic no-replace quarantine and
publication, durable journal ordering, restart reconciliation, and explicit
platform support. Until then, callers must not describe restore as
concurrency-safe or crash-safe. A future refusal must propagate through the
CLI, network/public sync, and pack restore callers without reporting success.

The proposed protocol and security limits are documented in
[`scv_workspace_restore_mutation_owner.md`](../05_design/scv_workspace_restore_mutation_owner.md).
Adversarial cases and the current evidence boundary are in the
[`non-executable BDD plan`](../03_plan/sys_test/scv_workspace_restore_mutation_owner.md).
The existing restore spec contains read-only preflight scenarios and a legacy
destructive restore scenario; neither is evidence of safe mutation:
[`scv_restore_spec.spl`](../../test/03_system/app/scv/feature/scv_restore_spec.spl);
runtime qualification remains **NOT_RUN**.
