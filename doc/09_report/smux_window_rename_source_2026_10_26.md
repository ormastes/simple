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


## Cycle 2: nonunique display names (2026-10-26)

**WARN / NOT_RUN: five unit and two owner integration cases, zero executed.**
The cycle-1 description and its freeze/review pins above remain historical.
Root corrected the initially approved collision policy after primary tmux
reference review: [Getting Started, immutable wiki revision
cf5a82fad1144475335e078548b6ed18fc37422c](https://github.com/tmux/tmux/wiki/Getting-Started/cf5a82fad1144475335e078548b6ed18fc37422c)
explains that window names need not be unique. This correction supersedes the
cycle-1 peer-name/peer-ID refusal; it does not weaken canonical clean-name rules.

At source baseline `1aaec595d0f49a0e255e27a6ebc5a7720f8cfa80`, the pure metadata
owner removes only its collision loop. Duplicate labels, cross-session labels,
and labels identical to another window's ID are allowed. ServiceState's
find_window_idx compares window.id; interactive_protocol similarly compares
candidate.id, while the remote select-window route takes window_id. The
session_targets owner resolves session identities, not window display names.
Frozen MuxObjectRefV1 identifies kind/object_id plus owner incarnation. Therefore
a display label must not acquire target authority or displace an ID lookup.
Future CoreMux ResolveTarget name matching must return InvalidTarget on ambiguity;
that pending adapter behavior is not implemented or claimed by this correction.

The updated unit case checks duplicate labels, unchanged distinct IDs and exact
ID lookup, then changes the actual sibling while an earlier window displays its
ID. The owner-integration case checks the same real API path and four actual
label changes: Unicode, ID-like label, sibling label, duplicate label. Repeating
a label and invalid/control/foreign-session requests leave the revision unchanged.
Membership, validation, geometry/zoom/presentation, content/child authority and
the separate live-child scenario remain intact. API publication and common
contracts are unchanged by this lane; concurrent L1/L2 owner changes are excluded.

Cycle-2 freeze: `build/review/smux-window-rename-source-v2.sdn`. No builds, tests,
compiler/runtime/provider/helper launches, staging or commits were performed.
Native assertions, canonical docgen, error-path cleanup and full CoreMux endpoint
qualification remain NOT_RUN; source acceptance is not feature execution.
