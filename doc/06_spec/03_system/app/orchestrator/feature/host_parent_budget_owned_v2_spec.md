# Owned journal parent-budget persistence V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests or builds were executed.
Requirement trace: `HOST-HELPER-04`.

Source APIs: `host_parent_budget_store_owned_v2`,
`host_parent_budget_load_owned_v2`, and `host_parent_budget_authorize_owned_v2`
in `src/lib/nogc_sync_mut/orchestration/host_parent_budget_v1.spl`.
Spec: `test/03_system/app/orchestrator/feature/host_parent_budget_owned_v2_spec.spl`.

The existing `host_parent_budget_fixture_v1` supplies genuine retained parent
allocation, signed grant/approval, current policy and an actual Linux journal.
The specs call the owned APIs with that capacity, scope and policy, and read
records back through the actual retained journal dispatch.

| Authored case | Intended assertion |
|---|---|
| Signed roundtrip | Exact signed bytes store/load and idempotent publication preserve the budget reference without helper publication or provider effects |
| Forged signatures | Independently tampered issuer and approver signatures refuse before the budget-record directory exists |
| Fresh publication context | Refresh expiry, changed policy context and clock regression refuse before publication |
| Fresh reload context | Previously published bytes convey no continuing authority; expiry/context/clock refusals preserve original bytes |
| Immutable conflict | A different genuinely re-signed envelope for the same budget digest passes authorization but cannot replace the original stored record; readback remains exact |
| Parent and scope binding | Wrong selected parent, invalid digest and changed host incarnation refuse without changing retained bytes |

The conflict fixture uses the same deterministic test-only issuer/approver keys
as the signed fixture and production Ed25519 signing for the changed messages.
It separately calls actual authorization before checking conflict, preventing a
forged-signature rejection from masquerading as immutable-publication coverage.

Scope is **generic owned-dispatch behavior using the actual Linux fixture**.
There is no fabricated Windows root, native Windows store, enrolled deployment,
connection capability or helper effect. These authored cases provide **no native
Windows qualification**. The new retained-journal dispatch foundation must be
integrated before execution; its current unlanded state is not test evidence.
