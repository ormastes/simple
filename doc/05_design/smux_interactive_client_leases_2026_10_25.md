# Interactive attachment leases

Status: authored candidate; genuine Phase 3 execution remains blocked. This
implements the selected N2 interactive lifetime boundary, not qualification of
every CoreMux provider or every legacy attachment.

`client_leases.spl` owns pure four-entry state transforms. Each identity combines
canonical session ID, client ID, secure owner incarnation and monotonic counter.
An opaque token is the 32-character lowercase hex incarnation, a colon and the
positive decimal counter. The API initializes the incarnation with checked
`sosix_random_hex(16)` on first leased admission. The new SOSIX entropy facade
only re-exports the existing checked crypto owner; it introduces no raw foreign
call or environment read. The admission boundary follows the checked crypto
owner's explicit nil guard and concrete text binding, avoiding nullable-pattern
inference at this critical check; optional payload lowering debt is recorded in
doc/08_tracking/bug/if_val_optional_payload_owner_2026-10-10.md. This does not
claim a new compiler reproduction or a qualified fix. Entropy failure refuses admission. Reset discards the
incarnation and requires fresh entropy before another leased attachment.

API admission atomically commits a new lease and attachment. Re-admission of the
same client ID rotates the token and clears its prior recipient queue, even in
the same session. Legacy `smux_attach` remains persistent/unmanaged and refuses
an existing leased ID, so a tokenless size request cannot silently downgrade
lifetime ownership. Interactive clients must use the leased route.

`smux_client_heartbeat` and `smux_client_resize_leased` require the exact identity
and a timestamp strictly before expiry; activity at the deadline cannot revive
an expired lease. Resize validates dimensions before committing either owner.
`smux_detach_leased` checks the token, including for an expired but not yet reaped
attachment, so delayed old-client teardown cannot detach a rebound client.
`smux_client_check_lease` performs the same identity/expiry check without renewal
or mutation, for tokenized notification polling and acknowledgment. Polling
cannot extend a crashed controller's lease or let its old token consume a
replacement client's messages. Legacy administrator access retains the shared
server-credential boundary.
Administrative detach remains explicit and also removes the lease. Successful
session teardown removes its leases; pending child cleanup does not falsely
claim session destruction. Closing sessions reject admission and renewal.

All real timestamps come through `sosix_time_now_monotonic_ms`; negative or
regressing timestamps and overflowing deadlines fail closed. The pure helpers
accept timestamps and nonce values for deterministic tests using the same
production transformations. They do not invent a test registry or provider.

The owner TTL is 15000ms, client heartbeat period 3000ms and server sweep target
1000ms. `smux_reap_expired_clients` proposes expiry, rechecks exact token and
deadline, removes only matching attachment metadata and queued notices, then
commits once. It never closes pane or process owners. Removing the attachment
also removes its size constraint from the existing frame arbitration. Sweep
errors are reported by the server without terminating background child owners.
These targets depend on event-loop progress and are not real-time guarantees.

Wire integration is root-owned: `client-attach SESSION CLIENT COLS ROWS` returns
`smux: leased TOKEN SESSION_ID`; the controller binds the canonical session ID
so rename does not disconnect it. Heartbeat, size update and detach carry the
token. Every post-admission controller operation uses a validated client-request
envelope, including frame reads and input mutations; stale incarnations cannot
address reused pane IDs before their next heartbeat. Independent heartbeats
renew the lease even when pane content does not change. Server periodic housekeeping runs even when
no client sends traffic. The global server credential remains the authentication
boundary; a lease is a freshness capability, not proof of user identity.

Acceptance source is `test/03_system/tools/smux_client_leases_spec.spl` with nine
authored helper/API/protocol scenarios. Live client-kill, restart and background
child survival evidence remains mandatory and has not been produced.
