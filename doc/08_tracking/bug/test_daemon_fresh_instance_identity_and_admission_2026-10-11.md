# Test daemon fresh-instance identity and admission follow-up

Date: 2026-10-11. Status: **OPEN**. Scope: Phase 1 bottom-up multi-session lane.

The coordinator reports cycle-one execution of
`test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl`:
kind/architecture isolation and shared bookkeeping passed; fresh identity and
fresh capacity failed. Retained evidence: `build/phase-one-ui-diagnostic/test_daemon_multi_session_system_spec/cycle-one.log`,
with adjacent `cycle-one.rss.env`, `cycle-one.exit`, and
`cycle-one.command.json`; input identities are in
`build/phase-one-ui-diagnostic/platform-daemon-inputs.json`.
The identity assertion and stopping the first instance fail because both
identical fresh requests have the same ID. The cap scenario counted three
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

Evidence is mixed-snapshot: the first two scenarios retain baseline PASS, and
the unchanged identity scenario retains baseline FAIL. Neither those scenarios
nor the complete revised seven-scenario file was rerun. Capacity is qualified
only at this focused broker bookkeeping scope; this bug remains OPEN for
identity and the related admission/adapter lifecycle gaps.

The identity defect remains: `session_types.spl:session_key_to_id` is a
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
The original fresh-identity regression remains an ordinary failing assertion,
not an expected-failure marker or skip.
