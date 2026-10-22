# Fenced artifact owner recovery candidate

REQ-IM-007; owner: Astra feature acceptance lane. Merge owner: root; final
reviewer: higher_model_coverage_review. Sidecars: N/A. No compiler launch allowed
in this lane. Maximum three repair/check cycles; initial patch is cycle one.

The retained finite model demonstrates that repeated claims after an owner stops
completing cannot recover its leased entry. That negative remains intentional:
generation advance is not death proof. This candidate consumes the existing
broker's durable collected-tree proof through a separate parent-owned API.

Recovery exposed another concrete bug: the bridge formerly looked up the current
lease for every result. A delayed original result could then inherit successor
authority. Recovered entries now require an explicitly supplied original dispatch
lease. Ordinary API callers remain compatible; a recovered caller omitting the
lease fails closed. Source call-site audit found no existing recovery consumer;
runner wiring remains a separate incomplete integration task.

Changes: artifact service generation tombstone; bridge publication lease fence;
new recovery owner; executable receipt-fixture scenarios and mirrored manual;
append-only recovery design clarification. Prior claim-atomicity commit
`bbc638149f8` is retained unchanged except the bridge's necessary publication API
extension. No unrelated work is included.

Acceptance authored: successful reap/requeue, original immutable route, released
reservation, successor dispatch and exact-lease completion, original completion
before recovery, stale/missing lease after recovery, stale-generation claim,
unchanged independent action, terminal-state rejection, absent/live/incomplete/
wrong-identity/differently-bound receipt, eight binding mismatches, and a split
coordinator token. Actual SSpec and docgen execution remain UNRUN.

Limits: no actual process killed; no crash-restart journal implementation; no
production spawn/dispatch integration; no performance evidence. This is a
reviewable implementation of the proof-consuming transition, not full recovery
qualification or a PASS for any of the nine incremental-build feature groups.
