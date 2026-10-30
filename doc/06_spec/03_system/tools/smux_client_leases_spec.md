# Interactive attachment lease scenarios

**TEST_BLOCKED — authored source/manual; compilation, execution, docgen and live
client-kill recovery have not run.**

Source: `test/03_system/tools/smux_client_leases_spec.spl`.
Requirements: `REQ-CMUX-002` (attachment lifecycle), `REQ-CMUX-003` (notification scope), and `NFR-CMUX-006` (crash/stale identity recovery).

The nine scenarios use production lease arithmetic and actual service APIs.
Deterministic time is supplied only to the same pure transforms used by the
production API; no test replaces the attachment registry or backend.

1. Admit at monotonic time 100, renew at 3100, and observe deadline 18100.
   A foreign session or regressing clock refuses. Equality expires the lease;
   neither a heartbeat at the deadline nor one after removal revives it.
2. Admit four clients, refuse a fifth, and remove four exact expired identities.
   A new admission uses generation five and recovers capacity.
3. Collect an expiry candidate, rebind the client, and reject the old candidate
   and heartbeat. Detach/reattach advances the counter. A fresh owner nonce
   rejects the previous owner's token even when both counters equal one.
4. Refuse missing/malformed owner entropy, malformed token framing, negative
   time and a deadline that would overflow.
5. Use actual leased attachment APIs to replace an attachment, refuse the old
   client's heartbeat/resize/detach and refuse tokenless downgrade. A live token
   resizes successfully; a separate legacy persistent attachment remains.
   Token-specific detach leaves the production pane ID intact.
6. Reset the actual service, reuse its session/client IDs, and require a fresh
   entropy-backed token. API and protocol heartbeat reject the old token.
7. Admit through `client-attach`, bind the canonical session ID from the reply,
   rename the session, and successfully heartbeat, resize and detach using the
   stable ID. The reply has four fields: `smux: leased TOKEN SESSION_ID`.
8. Rebind the actual attachment, then queue a fresh notification. The previous
   lease token cannot poll or acknowledge it. Its actual failed-heartbeat reply
   is rejected by `smux_remote_reply_ok`, not treated as a successful receipt.
   The current token still peeks the exact message, acknowledges it, and then
   observes an empty queue.
9. Validate every leased request before dispatch. A stale token cannot create a
   window or send input; current-token discovery succeeds. Foreign session
   commands, recursive envelopes and mismatched inner lease identities refuse
   without changing pane/window ownership. These are actual dispatcher calls,
   not evidence that a native terminal crash has been recovered.

`REQ-CMUX-006` capability discovery is a separate acceptance obligation; these
lease rows do not claim to verify the complete capability manifest.

Limits: four leased attachments at most (shared with the four-slot attachment
registry), 15-second TTL, intended 3-second heartbeat and 1-second server sweep.
These are configured deadlines and scheduling targets, not real-time guarantees.
Legacy API attachments are explicitly persistent/unmanaged; N2 interactive
admission must use the leased route.

Required live follow-up: start a background child and two native clients; kill
one client without graceful detach; observe its exact attachment, notification
queue and canvas constraint disappear after bounded server housekeeping while
the other client and child continue. Repeat after reconnect/rebind and server
restart; reject delayed old heartbeats and detach requests. Both tmux and native
providers need their selected CoreMux acceptance evidence. The authored helper
and API rows do not claim this live recovery or broader CoreMux qualification.
