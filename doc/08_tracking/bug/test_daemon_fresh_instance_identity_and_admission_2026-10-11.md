# Test daemon fresh-instance identity and admission follow-up

Date: 2026-10-11. Status: **Capacity and broker identity repaired at focused scope; lifecycle follow-ups OPEN**. Scope: Phase 1 bottom-up multi-session lane.

The coordinator reports cycle-one execution of
`test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl`:
kind/architecture isolation and shared bookkeeping passed; fresh identity and
fresh capacity failed. Retained evidence: `build/phase-one-ui-diagnostic/test_daemon_multi_session_system_spec/cycle-one.log`,
with adjacent `cycle-one.rss.env`, `cycle-one.exit`, and
`cycle-one.command.json`; input identities are in
`build/phase-one-ui-diagnostic/platform-daemon-inputs.json`.
In the baseline, the identity assertion and stopping the first instance failed
because both identical fresh requests had the same ID. The cap scenario counted three
leases where its independent QEMU/container budgets permitted two.

## Source evidence and bounded repair

`session_broker.spl` originally returned from `acquire` for fresh mode before
capacity checks. The current bounded repair skips only matching-idle reuse,
then applies capacity admission. Nonpositive capacity refuses admission;
if a reduced limit is already exceeded, admission refuses without evicting one
and replacing it while still above the limit. Three added regressions exercise
zero, fully active, and reduced capacity. Cycle two executed the original cap
scenario and those three added regressions: **4 passed, 0 failed, 435 ms**,
process exit zero. Retained log:
`build/phase-one-ui-diagnostic/daemon-capacity-cycle-two_spec/cycle-two.log`,
with adjacent `cycle-two.rss.env`, `cycle-two.exit`, and
`cycle-two.command.json`. Input manifest
`build/phase-one-ui-diagnostic/platform-daemon-cycle-two-inputs.json` binds the
production patch, canonical spec and diagnostic's extracted exact blocks.

Evidence is mixed-snapshot: the first two scenarios retain baseline PASS;
capacity has four passing cases at the cycle-two snapshot. The original identity
regression subsequently passed at the cycle-three snapshot below. Neither the
complete seven-case capacity revision nor current eleven-case file was run in
full. This report remains OPEN for admission/adapter lifecycle gaps.

The baseline identity defect was: `session_types.spl:session_key_to_id` is a
pure function of the reusable key, and `session_lease_new` uses that value.
`session_broker.spl:stop_session` removes every matching ID. The existing unit
freshness check only verifies count two; its uniqueness check uses different
keys and therefore does not detect repeated identical fresh requests.

## Required identity design constraints

- Preserve deterministic `SessionKey` identity for scheduler grouping/reuse.
- Allocate a distinct instance identity before adapter startup; adapters must
  participate in naming their external resources.
- Do not append a broker suffix to an adapter-returned lease ID. Container stop
  uses that ID as the Docker resource name. QEMU startup derives the QMP socket
  from the key in `adapters/qemu_adapter.spl`, and container startup derives its
  name in `adapters/container_adapter.spl`. Returned-handle renaming alone can
  orphan resources or target the wrong instance.
- Prefer an explicit instance field in the startup descriptor, or a consistently
  reserved descriptor configuration value with all owners updated. Broker/owner
  identity plus a per-start sequence must avoid same-time collision; changing
  shared key equality or relying only on wall-clock timing is insufficient.
- Represent refused/pending acquisition separately from a real admitted lease.
  Existing refusal returns an untracked default lease with deterministic ID,
  PID zero and idle status. It can alias an existing instance identity.

## Related lifecycle gaps, not repaired here

`daemon.spl` registers concrete adapters' `.base` values in the registry, whose
stored type is `SessionAdapter`. Its default start returns PID zero/idle and
execute reports failure; these bookkeeping scenarios cannot prove concrete
QEMU/container dispatch. Broker startup still tracks failed/default leases,
and the reuse branch can mark such a lease active without a successful health
check. `daemon.spl:handle_session_acquire` also reports completion for returned
leases without separating admission refusal. A complete repair must qualify
startup/health, adapter dispatch, pending response semantics and distinct
external resources, not just make the identity assertion green.

No runtime, socket, container, or cross-architecture qualification is claimed.
The original fresh-identity regression remains an ordinary assertion. Its
baseline failure and cycle-three PASS are both retained; it was not suppressed
with an expected-failure marker or skip.

## Identity repair, focused cycle-three PASS

`session_descriptor_new` now allocates an instance ID before adapter startup,
using the existing app I/O PID facade, time provider, and a module sequence owned
by the serial daemon control plane. This is not a concurrent allocator. The
reserved `__session_instance_id` configuration value carries the instance;
`SessionKey` equality and scheduler grouping remain unchanged. Missing instance
identity produces an empty-ID `LEASE_PENDING` without startup. Broker refusals
also use this non-addressable pending shape and do not enter the tracked pool.

Default, QEMU, container, service, hardware, remote-PC, and native/headless GUI
startup paths consume the descriptor identity. QEMU sockets derive from it;
container names derive from it and the returned actual container name remains
unchanged for reset/stop. No broker suffix is applied after adapter startup.
GUI container mode is explicitly excluded: its fixed `gui-test-session` name,
launcher-PID health/reset/stop and host-side execute do not implement actual
container ownership. Headless GUI's fixed display and hardware port sharing also
remain outside live isolation qualification. These exclusions prevent a claim
of uniqueness for all adapter-owned external resources.

Four added contracts cover descriptor allocation and default-adapter identity,
cross-broker instance separation, pending-handle non-aliasing, and malformed
descriptor refusal. Cycle three ran them plus the original fresh regression:
**5 passed, 0 failed, 895 ms**, process exit zero and guard quiescent one.
Evidence is `build/phase-one-ui-diagnostic/daemon-identity-cycle-three_spec/cycle-three.log`
with adjacent `.rss.env`, `.exit`, and `.command.json` receipts. The manifest
`build/phase-one-ui-diagnostic/daemon-identity-cycle-three-inputs.json` binds source,
canonical spec, and extracted exact blocks; retained production patch:
`build/phase-one-ui-diagnostic/daemon-identity-cycle-three.patch`.

All eleven scenarios now have passing evidence across three source snapshots:
two baseline, four capacity, five identity. This is not a complete-file run,
current-tree full PASS, native-product PASS, or live QEMU/container qualification.
Review found zero new P0/P1 issues. No fourth daemon cycle was performed.

P2: `src/app/test_daemon/daemon.spl:352–357` still constructs `TRESP_COMPLETED`
for every acquired result, including the new empty-ID `LEASE_PENDING`. Follow-up
must report explicit refusal or queue/retry pending requests, without treating
them as completed resource acquisition. `.base` dispatch, failed-start tracking,
GUI fixed resources, and hardware port sharing also remain OPEN.
