# Canonical shared client context — source candidate

Baseline `1aaec595d0f49a0e255e27a6ebc5a7720f8cfa80`. Source cycle 2.
**WARN / NOT_RUN: eight unit and three owner-API scenarios authored, zero executed.**
No compiler/native process/test/helper/watchdog launch or commit was performed.

This implements four approved production paths: the attachment record, pure
client-context helper, attachment transforms, and revision comparison. It does
not edit API or interactive owners. Root supplied the separately attributed API
publication hook, included in the freeze. Existing `_svc` is still the only registry.

The policy follows tmux's shared current window per session and active pane per
window. Attached clients use that shared input target, while identities and
viewports remain per client. See the [official tmux guide](https://github.com/tmux/tmux/wiki/Getting-Started#sessions-windows-and-panes).
The earlier private-selection proposal is retained with the superseding root
decision in `build/review/coremux-client-context-plan-v1.md`; it is not implemented.

`MuxClientAttachment` adds defaulted `attachment_generation`, `current_window`
and `current_pane`. Managed attachment creation copies the actual lease-issued
generation. Resizing preserves it; reattachment gets a fresh one. Unmanaged
generation zero cannot pass generation-checked lookup. Constructor compatibility
is preserved for dummy/refused attachment records.

`client_context_project` derives the unique session-active window and unique
visible focused pane. Detached/missing/ambiguous state projects empty IDs rather
than inventing focus; zoom must agree with the active pane. `client_context_put`
preserves ordered slots and always recomputes supplied context. Reconcile applies
this to all attachments. Lookup requires exact positive generation/session and
returns the current projection; it never authenticates, renews or mints a lease.
There is no private focus mutator or separate context controller.

Revision comparison includes generation and both context fields. Deadline-only
renewal remains excluded, and no-op reconcile preserves metadata equality.
Existing checked hide/close/terminate operations choose shared replacements;
this helper merely projects those committed outcomes without native effects.

## Required root integration before admission

Root's API hook now reconciles the final checked state before publication and the
single `_svc` assignment. Authenticated actor-specific focus must invoke existing
shared focus/zoom behavior and atomically updates all affected projections.
Closing and stale token checks remain owner requirements; the pure helper does
not grant input permission. Snapshot empty IDs become absent optional refs.

Interactive private next-pane/window cursors are an explicit remaining migration
gap. They must use shared owner context for rendering/input and preserve stale
input refusal without replay. CurrentContext and typed client-reference mapping
must authenticate the existing lease and generation. No independent selection
feature or partial CoreMux support is claimed.

The authored system cases exercise root's source-connected API reconciliation
without substituting helper calls for it. Their presence is not a passing integration test.
Native two-client input, failure/cleanup behavior, full CoreMux dispatch and N2
qualification remain required. Other authors' configured-launch files are untouched.

## Cycle 2 — public attachment return consistency

Independent source review found that successful `smux_attach` published canonical
context but returned a freshly constructed record with empty projection fields.
Root corrected the success return to the actual published attachment. The added
API scenario checks returned, stored and listed window/pane/generation after
initial attachment and changed viewport. It requires the expected nonempty target
and legacy generation zero; it does not manufacture a projected success value.
The immutable v1 manifest remains historical. No scenario was executed.

A further pure production-helper control covers managed reattachment into a
different session, fresh generation, old recipient clearing, refusal of the old
session token and refusal to downgrade the same label to unmanaged in either
session. This is explicit-state lease validation, not native authentication proof.
