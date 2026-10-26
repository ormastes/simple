# RenameWindow source candidate

Baseline `42690d6342b55c997efebb54a8508cc9921c0ae6`. Source cycle 1.
**WARN / NOT_RUN: five unit cases and two owner integration cases authored;
zero executed.** No compiler, runtime, helper, watchdog or native server launched.

`smux_rename_window(session_id, window_id, name)` now checks writable revision
authority and closing state, calls the pure `rename_window_state` transform,
captures its returned window, then publishes exactly once. `_svc` remains the
only service registry. The public API remains below 800 lines without compressed
formatting or an additional registry. Native child handles are never reopened,
replaced, closed or queried by the rename implementation.

The helper verifies exact session/window membership and refuses a name equal to
a different window's name or ID in the same session. It preserves the target ID
and every other window field, including zoom, manual reference geometry and
presentation. The identical name returns unchanged state, so publication does
not increment configuration. Other-session names are independent.

Canonical `request_validation_v1.check_text` already defines the CoreMux clean
name policy. The additive `mux_validate_name_v1` delegates to it unchanged; the
existing typed RenameWindow branch now uses that public helper. There is no new
ASCII restriction, shell quoting, whitespace restriction or duplicate validator.
Malformed UTF8 remains rejected by the existing canonical decoder; newly
authored boundary cases cover valid Unicode/byte counts and forbidden controls.

The system cases use actual API state and a real ConPTY child, with cleanup
before result assertions and computed child-output evidence. They do not invent
a network route or count source-authored cases as passing. Real failed/deferred
cleanup, native provider binding, canonical docgen, core/lib/MCP smokes and all
full CoreMux admission tests remain pending.

Current full adapter gap matrix: `build/review/coremux-server-adapter-plan-v2.md`.
It enumerates all 30 commands and nine other operations. RenameWindow closes one
owner gap; typed adapter dispatch, full capability admission and the persistent
CoreMux route are still unimplemented. The committed startup configured-launch
probe and typed resize results are recorded as dependencies, not runtime proof.
