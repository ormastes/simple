# Actual V2 controller proof and host correlation gates

Status: **NOT_RUN — awaiting verification**. Authored from executable assertions;
no native/admitted run, generated evidence or full dispatch PASS is claimed.

Spec: `test/03_system/app/orchestrator/feature/controller_container_authority_v2_spec.spl`.
Fixture: `test/fixtures/orchestrator_acceptance/controller_container_authority_v2.spl`.
Authored ORCH-02/HOST-02 labels map intended assertions pending existing requirement
reconciliation, not complete provider/security/NFR qualification.

## Setup and what is actually verified

The fixture builds canonical V2 assignments/requests and actually calls Ed25519
signing helpers for all four grants and all four approvals. The actual SDK snapshot
contains separate scoped controller issuer/approver and host issuer/approver keys.
The production controller authorizer verifies all four pairs using this typed
internal context. No zero-proof successful authentication fixture exists.

Synthetic now100 is an internal unit clock only. Approvals expire1100, grants1200,
keys2000. Real app time remains native Unix milliseconds. Typed host status,
validation projection and17-fact observation are constructed DATA, not native
queries or fake replacement host callables. Windows opaque body is common-wire
fixture data; it does not qualify Docker request semantics.

## Eight cases and concrete checks

Each step name mirrors its case title exactly.

| Case | Steps and expected assertions |
|---|---|
| Four actual signed actions | Invoke production authorizer; return assignment-renewed/execution-renewed grants. Require four scoped keys with distinct issuer/approver public keys for controller and host. |
| Invalid current proof | Independently forge each of eight signature frames, reuse preparation proof for execute, expire approval at1100, use unavailable time0 or revoke host issuer. Every actual authorization fails. |
| Host status correlation | Match actual schema for native and service scopes; reject changed alias/native ID/fence/provider/enrollment pin, string CPU, negative reservation count or availability beyond capacity. |
| Exact resource projection | Reject wrong platform backend, CPU/memory mismatch, nonpositive/excess timeout, unreserved devices, authorization=true and nonboolean workspace claim. Explicitly demonstrate proof verification is not backend semantic validation; actual core must call real host-validate. |
| Prepared/observed reply | Call actual response correlator on exact prepared state and full native-ID observation. Check host-prepared/runtime-observed status, exact nested hash/identity and rejection of false completion or incorrect prepared state. |
| Native identity/proof correlation | Reject empty/short running native ID, wrong host operation digest, engine, provider pin or exact new-execution grant ID. Read-only replay may correlate a prior grant ID but creates no execution authority. |
| Immutable replay retention | Use actual private temp filesystem and packet retain/load. Independently read expected assignment-digest path and exact bytes. Proof-sensitive authorization still rejects a forged packet even when immutable input equality is true; changed body cannot replace retained bytes. |
| Strict messages | Reject noncanonical, unknown, typed-version, duplicate and4098-byte status/validation inputs against4096-byte limits. |

The metadata/private-root install and actual journal/host lifecycle are separate
suites. This unit uses no fabricated backend projection callback: it calls actual
correlation functions with declared data. Such a matching data structure is not
proof that a provider parsed or executed a request. Source review confirms actual
core obtains real host-validate before capacity/journal admission and rechecks
current policy/time before effects; composed execution is still a separate gate.

## Assertion mapping and required integration

ORCH-02 maps to four actual action proofs, immutable replay bytes and current-proof
checks. HOST-02 maps to full alias/native/provider/fence correlation, exact reserved
resource/timeout projection and phase-appropriate native identity.

The host observation module is a pending host-owned source integration dependency;
no module is copied or stubbed to make this test appear runnable. Signed host
producer trust, private root publication, real CLI clock, ledger no-overcommit,
unknown outcomes/cancellation and backend API nonce/native-ID inspection remain
required. No build, live host/container action, admitted SSpec, SPipe maintenance,
coverage or full-system acceptance occurred.
