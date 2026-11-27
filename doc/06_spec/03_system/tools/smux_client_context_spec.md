# Shared client focus through the owner API

Source: `test/03_system/tools/smux_client_context_spec.spl`.
Requirements: REQ-CMUX-003/004/008.
**NOT_RUN: three authored scenarios, zero executed.** Root-owned API publication
integration is connected in source. The spec deliberately reads stored owner attachments;
it does not call reconciliation on behalf of an unimplemented integration.

1. Create two sessions. Attach two managed clients to one and a third to the
   other. Change shared pane/window focus and require both local clients to
   follow while the other session remains unchanged. Same-size renewal must not
   increment configuration. Delete the selected window and hide the selected
   pane; require stored context to follow the owner's actual replacement.
2. Reattach the same client label through actual managed API admission. Require
   a new attachment generation, refusal of the old generation, and unchanged
   shared window/pane focus.
3. Attach an unmanaged client and repeat with a changed viewport. Require the
   actual returned record to match stored and listed context/generation, with
   nonempty expected current window/pane, one listed identity, generation zero
   and the requested viewport. Cleanup precedes result assertions.

Each scenario releases only its owned sessions before asserting collected
results. No global reset or fabricated PID is used. These scenarios exercise
real persistent API state but launch no child; they are not native ConPTY input,
wire authorization, closing-failure, interactive compatibility or N2 evidence.
Real two-client child-output/viewport/lifetime cases remain required after root
connects authenticated focus and interactive routing to canonical shared state.
Canonical SSpec/docgen and core/lib/MCP checks remain pending execution.
