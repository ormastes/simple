# HIR worker admission and retirement

Status: NOT_RUN. Authored against release a1e831a2b569775db2193d53f686ea87cc5a2d23.
No native execution, compiler acceptance, branch coverage or latency qualification is claimed.

The integration spec prepares real SCV source authority and the existing canonical
closure/policy handoff for `test/fixtures/worker_hir_profile_v1/entry.spl`. It launches
the current executable through the retained V4 pin and existing internal worker
dispatch, requires an actual `.hir` output and verifies that linking did not run.
Cancellation and parent-observed deadline expiry use real retained workers and
must remain failed work outcomes after retirement. A controlled invalid-ticket
case retains the authentic local lease and restores it to clean up; this tests
facade rejection and does not inject a native signal/reap fault.

Run the integration file in an isolated native test process with the matching
compiler dispatcher and ProcessGroup V4 provider. Its fixture temporarily owns
and restores the complete environment. Unsupported providers are failures of
this qualification gate, not substitute passes. Failed retirement retains the
fixture and owner; do not delete its storage as if cleanup succeeded.

Required remaining evidence: actual native run with bounded outer supervisor;
execution of authored production coordinator positive/rejection cases; replacement and sibling cancellation tests;
full managed-tool configuration positive control; clock/pin-close/native cleanup
fault injection; RSS/latency measurements. The current canonical start facade
can lose a lease on malformed post-launch decode. The app reports uncertain
launch and blocks success but cannot repair that missing owner authority.

The initial profile covers a nonempty frozen HIR-only source closure. Generic
MIR/file/native-codegen workers and arbitrary escaping tools are not qualified
by these tests. Parent-trackable generic broker requirements remain open.

The production `native_build_hir_ledger_run_v1` path is now exercised directly by
a positive authored case with the canonical builder cache/no-stub settings and
a negative loader-injection case. The positive requires real ledger claims,
retirement and an actual HIR artifact. Sorting of the exact V4 environment and
controlled monotonic-clock rejection have paired assertions. All remain NOT_RUN.


E3 update: the actual consumer now uses the committed reservation facade
(a4610ebbbbb3bde8e8aff8ff85a5ba57da5b7f25), not the legacy lease startup path.
The rejected-ticket control is replaced by real observation/codec composition:
positive decode of the full provider observation, corrupted-version rejection,
early confirm refusal, malformed ack refusal, repeated valid ack, then release
and pin closure of the same reservation. This does not inject corruption inside
observe; the separate native C fixture supplies native publication/ack fault
coverage. All Simple/app cases remain NOT_RUN. Historical start/ack authority
loss is no longer an unaddressed source dependency for this migrated consumer;
actual Simple/native combined qualification and generic tool scope remain open.
