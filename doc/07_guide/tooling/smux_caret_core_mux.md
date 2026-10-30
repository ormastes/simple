# Caret CoreMux and smux candidate workflows

2026-10-25. Selected A/N2 requirements: doc/02_requirements/feature/caret_mux_tui.md and the NFR counterpart. Implementation and native qualification remain incomplete. Do not deploy these source changes as a verified tmux replacement.

## Ownership and backend selection

Use an independent smux owner for background sessions; the legacy stdin mode exits on EOF and is not a persistent workspace. The current product accepts --serve ADDRESS TOKEN, --request ADDRESS TOKEN VERB..., and --attach ADDRESS TOKEN SESSION CLIENT_ID. Keep the endpoint local and bind clients to the intended owner. Existing token holders share owner authority; the protocol does not identify human senders.

These verbs are smux protocol commands, not a completed tmux-argv compatibility layer. Caret's audited -L/-t/format/cwd/lifecycle calls still need the shared adapter. See doc/09_report/caret_smux_compatibility_2026-10-25.md.

## Candidate remote commands

Pass arguments separately through the product's --request interface:

| Verb | Arguments | Meaning |
|---|---|---|
| list-sessions | none | List stable session IDs and names; legacy list still returns the count. |
| has-session | SESSION | Resolve an exact ID first, otherwise an unambiguous name; absent/ambiguous targets fail. |
| rename-session | SESSION NEW_NAME | Keep stable IDs, panes and attachments. Names are bounded single tokens without whitespace or C0/C1 controls. |
| kill-session | SESSION | Close only owned children and remove only that session after native close confirms. Partial cleanup returns failure and retains handles for retry. |
| send-pane | SESSION WINDOW PANE COMMAND... | Submit a shell command to the exact owned pane without changing session/window focus. It is distinct from raw input, named keys or paste. |
| notify | SESSION CLIENT HEX | Queue bounded UTF-8 notification text for an attached recipient. Encode bytes as hex; do not send terminal escape commands. |
| notifications | SESSION CLIENT | Read the oldest notice without consuming it. |
| ack-notification | SESSION CLIENT ID | Consume only that recipient's oldest matching ID after successful rendering. |

The interactive client uses explicitly leased admission rather than persistent legacy attach metadata. `client-attach SESSION CLIENT COLS ROWS` returns `smux: leased TOKEN SESSION_ID`; subsequent requests bind that canonical ID and opaque token. The token includes a checked secure owner incarnation and increasing generation. Rebinding, reset/restart or expiry invalidates old client tokens.

Heartbeat is requested every three seconds, with a fifteen-second lease and a one-second server sweep cadence. These are configured scheduling intervals, not hard real-time guarantees. Expiry removes attachment capacity and size constraints and clears that recipient's notices; background pane children remain owned by the server. Clock/entropy failures return errors; the owner does not pretend to expire clients or terminate background work on a clock failure.

Every post-admission interactive command travels in a `client-request SESSION CLIENT TOKEN INNER_COMMAND...` envelope. It validates the current incarnation, expiry and target session before reads or mutations, not only on heartbeat. A stale terminal cannot type into pane IDs reused by a restarted server. Lease-specific notice polling/ACK and detach also reject superseded tokens. Raw shared-owner administrative commands retain their existing authority; this is not per-human authentication.

Legacy direct API attachments remain explicitly persistent/unmanaged for compatibility, and cannot silently downgrade a leased attachment. They do not establish N2 crash-recovery guarantees. New CoreMux client paths must use managed leases and expose attachment mode in their snapshots.

Notification storage is bounded to 32 messages of 1..1024 UTF-8 bytes. The terminal client filters controls, clips by display cells, and acknowledges after a successful console write. Acknowledgment failure may cause redelivery; exactly-once visible delivery is not promised. Explicit detach, rebind and reset clear affected pending messages. Required native rendering/ACK tests remain NOT_RUN.

Manual split rectangles now retain direction and nested placement through current-layout requests, frame refreshes and resize projection. Explicit named-layout selection intentionally replaces the plan. An impossible shrink or overlapping pane resize refuses before committing metadata. Failed shell startup uses a freshness-checked rollback checkpoint to retain the original reference canvas.

## Qualification and errors

The current instruction is to use a genuine Phase3 compiler and, if needed, rebuild Phase3 with Phase3; do not rebuild Phase2. Older Phase2-first examples in historical Windows composition reports are not the current campaign instructions. A path named stage3 is not lineage proof. Require matching producer/runtime receipts and actual Hello compile/run; general SSpec/docgen additionally needs a qualified full CLI or matching standalone runner.

Required Caret operations cannot become optional to mask an implementation gap. Optional terminal extensions may report Unsupported without mutation. Distinguish unsupported, permission denial, unavailable transport, invalid/stale targets, busy/timeout and partial commit. Do not silently switch backends or blindly replay a timed-out launch/delete.

N2 requires both backend cohorts, concurrency/recovery/slow-consumer controls and a real 24-hour soak each. No shortened run, source review, authored case count, successful command formatting or historical different-producer result qualifies that gate.
