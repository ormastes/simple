# Owner-bearing prepared helper expiry V3

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests, builds or native executions
were run. Requirement trace: `HOST-HELPER-01`, `HOST-HELPER-02`, `HOST-HELPER-03`,
and `AT-HOST-05` for the journal orderings below.

Spec: `test/03_system/app/orchestrator/feature/host_prepared_expiry_owned_v3_spec.spl`.
API: `host_capacity_owner_expire_prepared_owned_v3` in
`src/lib/nogc_sync_mut/orchestration/host_capacity_owner_v1.spl`.
The API is present on `release/1.0.0`.

The specs reuse the actual signed `host_helper_fixture_v1`, canonical helper
request encode/decode, real helper preparation and real signed begin path.
They do not import another executing spec module or fabricate owner state,
Windows root capabilities, cancellation grants or native completion evidence.

| Exact authored test name | Intended assertion |
|---|---|
| refuses an admitted helper before its actual prepare deadline without mutation | One tick before the retained deadline returns `prepare-not-expired` with the original journal lease, sequence, ledger and admitted charge |
| expires only the selected prepared helper at its deadline and preserves parent and sibling charge | Exact-deadline release commits one cancelled outcome, returns the current journal aligned with ledger revision, and frees only the selected helper's CPU/memory |
| refuses expiry of an executing helper and keeps its actual charge | A genuinely signed begin yields executing state; the preparation timer returns `execution-reconciliation-required` with ownership and resource charge retained |
| retains the unchanged owner for missing operations and invalid timer values | Unknown/empty operation IDs and negative timer values refuse while preserving the returned actual owner and existing admitted reservation |

The successful case creates a second genuinely signed sibling helper, then
checks that both its reservation and the parent reservation remain unchanged
and charged. It checks the returned journal's cancelled operation, incremented
sequence, unchanged lease identity, and ledger revision equal to sequence plus
one. The original signed execution request arrives one monotonic tick after
expiry. It must return no lease and preserve the cancelled operation, released
capacity, and exact owner. In the opposite ordering, a signed begin consumes
the reservation first. Expiry and replay of the authorization preserve the
executing state and charge and yield no second lease. Every case closes the
actual returned owner.

Scope is the generic expiry contract through the real Linux signed journal
fixture. Beginning helper execution here records ownership and a signed lease;
it does not launch a native helper or Engine operation. These authored cases
provide no native Windows qualification or runtime PASS claim.

The post-commit projection-error path remains unexercised: no legitimate fixture
currently induces that failure after a successful durable outcome without
fabricating or corrupting ownership. This manual does not claim fault-injection
coverage. The API's owner-bearing error return still requires independent
native/integration evidence for that exceptional branch.
