# smux session targeting and attached-client notifications

Status: source implementation and authored SSpec; Phase 3 execution remains blocked. User scope explicitly includes both pane text/commands across sessions and visible notifications to attached clients. These are distinct delivery channels; neither creates an inter-user identity system.

## Required behavior and ownership

| Requirement | Production owner | Evidence |
|---|---|---|
| REQ-SMUX-MESSAGE-001: discover stable targets and reject ambiguous names | session_targets and remote list-sessions | Production protocol cases |
| REQ-SMUX-MESSAGE-002: send to an explicit inactive/detached pane without changing another view | remote send-pane and existing input SESSION WINDOW PANE HEX | Ownership refusal and real Windows child-computed result |
| REQ-SMUX-MESSAGE-003: queue bounded notices for an actual attached session/client pair | notification_protocol and client_notifications | Scope, token, payload and capacity cases |
| REQ-SMUX-MESSAGE-004: retain oldest notice until acknowledged after rendering | queue peek/ack and interactive client | Queue retry/order cases; real console delivery pending |
| REQ-SMUX-MESSAGE-005: clear notices on actual detach, session rebind and reset | API lifecycle hooks | Actual service lifecycle cases |
| REQ-SMUX-MESSAGE-006: render Unicode within terminal cells without interpreting payload controls | notification_client and client_clip_line | Real decoder/overlay cases; Windows console painting pending |

`client_notifications.spl` owns a process-local array of at most 32 records. Each body is 1..1024 UTF-8 bytes, bounding stored body data to 32 KiB. Monotonically increasing signed 64-bit IDs stop admitting entries before overflow. Reset clears records without rewinding IDs. Queue mutation is synchronous in the existing single server owner; no threads, background callbacks, persistence files or new transports are introduced.

Each record carries ID, canonical session ID, client ID and body. There is deliberately no caller-supplied sender field. The existing loopback server token authorizes notification operations. Every holder of that shared token has the same authority, including reading/acknowledging another attached client's queue; client identifiers are routing labels, not authenticated user identities. The production protocol validates the actual attachment pair before enqueue, peek or acknowledgement.

## Commands and wire behavior

| Command | Semantics |
|---|---|
| `list-sessions` | List stable IDs and names; retain existing count-only `list` compatibility |
| `send-pane SESSION WINDOW PANE COMMAND` | Existing command delivery with Enter to an explicit owned pane; no focus mutation |
| `input SESSION WINDOW PANE HEX` | Existing exact UTF-8 input, including control bytes; no automatic Enter |
| `notify SESSION CLIENT HEX` | Queue a visible notice for an attached recipient |
| `notifications SESSION CLIENT` | Peek oldest notice without removal |
| `ack-notification SESSION CLIENT ID` | Remove only that recipient's exact oldest ID |

The existing SMUX/1 byte framing and authenticated request dispatcher remain authoritative. Payloads use the existing strict UTF-8 hexadecimal codec, avoiding line delimiters or a second escape format. Notices return `smux: notification ID HEX`, or exact `smux: notification none`. Queue and acknowledgement replies carry positive canonical decimal IDs. The success classifier validates full response structure rather than accepting arbitrary success-looking prefixes.

Session resolution gives exact IDs precedence; a name resolves only when unique. This avoids a name matching another session's ID or duplicate-name iteration order selecting the wrong target. Names remain command tokens; space-bearing session names are not newly introduced here.

## Delivery and display

The interactive client polls every 250 ms while no notice is displayed. It appends a bottom-row notification overlay to its real frame/copy viewport and shows the notice for three seconds. It acknowledges only after the console owner reports successful writing. A failed write cannot acknowledge. A failed acknowledgement does not establish exactly-once delivery; client failure/detach can discard queued notices. This is best-effort attached-client notification, not durable messaging.

Rendering uses existing scalar iteration and terminal-cell width clipping. C0 and C1 payload controls, including ESC, CR, LF and BEL, are filtered; wide glyphs are not cut into partial UTF-8 bytes. The overlay saves/restores cursor position, clears its row, and uses only fixed owner-generated ANSI sequences. Arrival and expiry change the combined frame so the base terminal content is repainted.

Actual detach clears only that recipient. A same-session size update preserves notices; a rebind to another session clears the old recipient. Service reset clears all queued notices. Session deletion is not implemented by this change and must invoke equivalent cleanup when added. Existing absence of attachment leases means an abruptly terminated client can retain an attachment and queue until explicit detach; this remains a lifecycle gap.

## Validation and remaining scope

`smux_session_messaging_spec.spl` contains production API/protocol/queue/render-helper scenarios plus one Windows-only real ConPTY case. The latter sends a variable-setting command and a variable-dependent arithmetic command to an inactive detached target pane, requires the computed result 5859, and checks both session focuses. Capturing while waiting verifies addressed command delivery, not unattended owner draining; existing external-owner scenarios own that separate claim.

All new specs are authored, not executed. Native Phase 3 product/runner selection, generated-manual freshness, actual client notification painting and ACK timing, external-owner shutdown and resource limits remain required. No compiler launch, runner stub, fake process or copied implementation oracle establishes a PASS. Rename/kill session/window commands, automatic owner discovery and crashed-client recovery remain separate missing session-management features.
