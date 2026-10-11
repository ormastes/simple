# UI interaction state and access integration

Executable: `test/03_system/gui/ui/interaction_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`.

Status: **Phase1 seed diagnostics PASS, 4/4**. Evidence:
`build/phase-one-ui-diagnostic/interaction_spec/cycle-one.log`. This manually
maintained guide does not claim native qualification, live browser delivery,
measured coverage, or completed docgen.

1. Build a real widget tree with root focus. Encode a `j` keypress, then dispatch
   it through `update_state`. Require focus to move to the action button, then
   to the input after another `j`, and back to the button after `k`. Rebuild
   access snapshots after each transition and require exactly one focused node.
   Envelope checks prove encoding; state checks independently prove dispatch.
2. Require the real button to be initially visible. Hide it through the widget
   owner and rebuild the snapshot: existence must still succeed, while visible
   must fail. A missing identity must fail existence. Showing the widget must
   restore the visible verdict.
3. Hit-test a target input in a three-row tree, dispatch drag start, move, and
   drop through the production state owner, and check source/target flags.
   Require the target's previous value to become the payload, the sibling input
   to remain unchanged, and all drag flags to clear. The access ensure engine
   must also observe the delivered value. Preserve envelope assertions, including
   the distinction between encoded source ID and coordinate-selected receiver.
4. Append source and target events explicitly to the access history model.
   Require both records, their original order, sequence numbers, and payload.
   This proves history retention only; it does not prove that the state reducer
   automatically records events or delivers content to a list.

Indexed assertions require exact list lengths before accessing elements.
Coverage annotations declare 80% targets for the production event, access, and
envelope owners; no measured coverage or passing scenario counts are claimed.

The canonical spec subsumes the legacy
`test/system/ui/interaction_spec.spl` keyboard-envelope, access-ensure, and
drag-envelope assertions; that duplicate is removed. The previous canonical
spec's ordered-history checks are retained with an explicit model-only scope.

Live browser event transport, visible renderer feedback, and end-to-end dragging
onto a navigation list remain unqualified. The production reducer exercised
here delivers content to input/textfield widgets; model history cannot close
the broader interaction requirement.
