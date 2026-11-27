# Host helper one-use output and settlement

Status: NOT_RUN / AWAITING_VERIFICATION. No build, native execution, performance
measurement or successful settlement is claimed for this slice.

Source: `test/03_system/app/orchestrator/feature/host_helper_settlement_v1_spec.spl`.
Fixture: `test/fixtures/orchestration/host_helper_settlement_fixture_v1.spl`.

The eight executable source cases cover:

1. Full consumed-plan canonical roundtrip, malformed encoding and packet/outer
   plan substitution rejection.
2. Real exclusive file consumption: identical retries and partial existing
   records block a second launch opportunity.
3. A rejected native outcome stays retained/charged and receives no absence ACK.
4. Missing actual terminal proof preserves the full owner and journal charge;
   no settlement record or ACK appears.
5. Reference generation/root/identity metadata substitution is rejected before
   native cleanup. The original reference may legitimately already be retired.
6. Malformed and dangling native archives refuse metadata recovery and remain
   unchanged. Recovery never replaces a present bad record.
7. A stale journal writer cannot repair/publish a missing native archive.
8. Metadata recovery reconstructs no live helper lease/ref; same-ID operation
   field substitution is rejected before settlement.

The fixture uses the existing real helper Ed25519 signatures and journal owner.
Parent execution setup uses the trusted capacity primitive solely to enable the
actual attach-helper admission test. Planning paths and native IDs are synthetic
metadata. `group_process_stream_prepare_v2` writes only claim/request metadata;
no helper child, cgroup, terminal receipt, resource-enforced execution or positive
cleanup authority is simulated. The fake completed journal digest in the stale
writer test is explicitly not native proof and must not release capacity.

## Required supported-host integration (NOT_RUN)

Use a real authenticated host journal, signed helper request/parent budget,
protected broker image and delegated cpu+memory cgroup parent with sibling broker
overhead scope. Missing delegation is a rejection, not a successful test.

- Open once through `host_helper_open_output_v1`. Retain its sole actual native
  outcome. Invoke the same helper again and verify consumption prevents a second
  provider call, including identical bytes and partial-consumption recovery.
- Force native metadata publication to fail after an actual Ready or
  CleanupRequired return. Verify the turn retains that exact owner/ref outcome
  and unchanged charge. Remove the fixture-owned obstruction; recover from the
  consumed exact root and actual broker request/claim, never relaunch.
- Before real terminal proof, settle and verify no cancellation/native retirement,
  no ACK and no capacity release. Let the sole reader/smux perform its actual
  cleanup; obtain real cgroup/pidfd/no-child canonical proof from the broker.
- Settle after proof (including after grant expiry). Verify exact owner-only
  descriptor retirement, canonical grouped reap and host journal completion.
  ACK must bind helper operation, outer request, prepared receipt, native identity,
  tree digest, outcome digest and the actual returned journal revision/sequence.
- Retain the original typed bundle for an exact completed replay using the latest
  returned host owner. Verify idempotent same outcome/tree digest, no duplicate
  journal append, and a correlated ACK; no Some(ref) stale retry is used.
- Reopen the host journal and independently verify the same outcome before the
  projection releases capacity. Tampered consumed/native identity or missing
  broker/reap evidence must keep it charged. Preserve every audit artifact after
  ACK; heartbeat/grant expiry is never release proof.

All phases are bounded calls with no polling, full-tree scan or retry launch.
Live/recovered bundle validation and the pre-native settlement phase deliberately
reload metadata independently; within each phase the validated context/native is
shared. The hook/reopen validator performs a separate fresh reload before journal
commit/projection. A record is bounded to 8 MiB, request to 2 MiB, broker request
to 16 MiB and reap evidence to 16 KiB by existing codecs. These finite safety
boundaries have not been benchmarked. This is the existing process-crash journal
profile, with no new power-loss durability claim.

## Checkpoint boundary

This is an in-process, sole-writer host checkpoint. The open and settlement
entrypoints receive the current host journal owner directly; they are not an
independent daemon gateway or signing/IPC service. Those gateway, signing and IPC
connections remain missing and are not implied by these typed data ports.

The dangling archive fixture uses the actual snapshot-link provider: create an
existing confined regular target (kind 1), create and match its exact relative
link, then delete the target with the file facade. After refusal, create-exclusive
must still fail at the dangling link entry. The unsupported generic filesystem
symlink helpers are not used. No new native code or shell setup is involved.
