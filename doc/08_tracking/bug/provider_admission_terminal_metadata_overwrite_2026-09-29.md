# Provider admission terminal metadata overwrite

Status: corrected; production verification blocked. Owner: Codex items_4_5.

REQ-002 and REQ-012 require fail-closed provider admission. In
`src/compiler/99.loader/provider_admission/state.spl`, publish/reject mutate
metadata before attempting their state transition. A refused second publication
therefore replaces the accepted receipt; a refused rejection can add a failure
to an admitted provider. This violates cached terminal-state integrity.

Acceptance: claim the finalization state atomically before metadata mutation;
readers must see finalization as admitting until release publication completes.
Test duplicate publication and both opposite terminal-state attempts using the
actual state owner. State-only fixtures do not establish artifact admission,
native provider loading, or concurrent lifetime qualification.

## Correction and diagnostic evidence

Both terminal writers now reserve internal state `3` with acquire/release CAS
before mutating metadata. The public state reader treats `3` as `admitting`;
release-store publishes admitted/rejected only after the winning metadata write.
Losing writers return without mutation. No new failure-return branch exists
after reservation. As before, catastrophic failure during publication leaves
waiters subject to the bounded wait budget rather than fabricating admission.

Windows Phase 1 interpreter diagnostics, 2026-09-29:

- Initial test invocation executed zero examples because the existing
  `app.spipe.testing` import no longer resolved. The spec now uses `std.spec.*`.
- Before production correction: 12 executed, 9 passed, 3 failed, exit 1.
  Duplicate publication replaced `primary` with `replacement`; both opposite
  terminal transitions incorrectly attached metadata despite returning false.
- After correction: 13 executed, 13 passed, zero skipped/dropped, exit 0.
  The additional reserved-state example checks that competing publication and
  rejection cannot publish metadata while readers still observe `admitting`.
- Phase 1 SPipe docgen: one complete mirrored manual, zero stubs, exit 0.
  The four new state scenarios and their imperative steps were inspected.

Logs: `build/native_probe/provider-terminal-integrity/`.
Runtime SHA-256:
`6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
These are deterministic state-machine diagnostics with the authorized seed,
not native thread contention or production admission evidence. Remaining
unblock condition: admitted self-hosted verification, required core checks,
and native provider lifetime/concurrency qualification.
