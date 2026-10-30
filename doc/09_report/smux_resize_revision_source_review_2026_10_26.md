# Resize revision admission: local source review

Status: WARN / NOT_RUN. Root-authored patch and local review; no independent Astra acceptance. Astra service returned a usage-limit error before completing this lane. No compiler or process execution is inferred from this report.

Base: `9ce3db18d9b7c61c80c4aba1447a7969afb0f019`. The private freeze manifest `build/review/smux-resize-revision-source-v2.sdn` binds exact working-file hashes after added presentation/rollback controls. The v1 manifest is historical. Unrelated configured-PTY probe edits are excluded.

## Source reasoning

The pure viewport projector admits all dimension-changing participants before allocating resized grids and propagates Result failures to its layout, presentation and pane-removal callers. Direct resize no longer performs an unchecked preliminary record resize. The geometry commit evaluates the projection before native calls, then the native transaction separately validates capacity against the original records before its first effect. This avoids treating service configuration revision as pane content capacity.

Checkpoint rollback invokes that same complete transaction validation before resizing retained records. It preserves current child identities, output and focus through the existing checkpoint guards; exhaustion refuses rather than restoring stale content. Native resize compensation retains its existing uncertain-result handling. Exact same-size record resize now returns the existing record, so no-op projection cannot clear frozen state or consume an identity.

A bounded call-site search found record resize in checked viewport projection, checkpoint rollback after shared admission, and initialization of a fresh split record. The backend terminal-shell resize is a separate owner. This is source inspection, not proof of runtime value-copy semantics or OS-call ordering.

## Authored evidence and limits

Eight explicit-state scenarios cover exact no-op, exhausted projection, exhausted transaction, direct planning refusal, final identity then refusal, a later exhausted participant, presentation border refusal, and checkpoint rollback refusal with retained pane ownership. They call production functions with explicit state. There are no real native handles in these cases. None has run; generated-manual and SSpec-maintenance checks are pending.

Remaining gates include compilation, real multi-pane viewport and rollback observations, captured screen stability, cleanup, independent review, the existing zoom/presentation/lifecycle suites, and full CoreMux qualification. The tracking bug remains open. The patch must not be reported as a passing system fix or used to admit the incomplete provider.
