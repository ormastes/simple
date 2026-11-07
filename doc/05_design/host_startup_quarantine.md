# Existing-ledger startup quarantine

`host_capacity_owner_open_quarantined_v2` opens the existing distributed-operation
journal under its exact writer lease. It is a startup mechanism, not an admission
capability. The returned ledger has `continuity_proven=false` and therefore cannot
admit new work or reconstruct a prepared receipt.

Physical host and capacity authority must still match every retained intent.
Different opaque boot/service fences and provider generations are accepted only
for quarantine: every retained row becomes uncertain and remains charged.
Executing journal rows use the existing recovery transition to outcome-unknown.
Admitted rows remain admitted in the journal, preserving the distinction between
known no-execution-intent and possible native effects for later reconciliation.

The ordinary open path remains strict and rejects a changed fence. Receipt and
execution checks now explicitly compare retained authority/fence/generation to
the current capacity owner, so old prepared receipts cannot become valid merely
because a new owner has read the same journal.

The persistent service must acquire actual bounded backend inventory, quarantine
all ambiguous scope entries and retain a current service incarnation before
enabling admission. This patch does not provide such readiness, adopt a native
resource, or release capacity. Explicit reconciliation must eventually resolve
admitted no-effect intents separately from executing/unknown intents and retain
the exact native absence or process-reap evidence needed for release. Those
service and settlement consumers remain ongoing work, not a completion claim.

The added scenario in `host_signed_prepare_spec.spl` exercises both prepared and
executing rows across changed fences, writer reopen and exact charge checks.
It is authored **NOT_RUN**; no compiler/runtime qualification is claimed.

Historical released allocations may sum above the physical ceiling. Quarantined open now validates their row/identity shape without requiring the uncertain total to fit, so actual reconciliation remains reachable. Every returned row stays charged and continuity stays false; querying availability returns capacity-exceeded until proven no-effect history is released. No over-capacity admission is enabled. The authored three-generation prepare/expiry/reopen regression is NOT_RUN.
