# Windows Host composition V3 acceptance inventory

Status: **AWAITING_VERIFICATION / NOT_RUN**. No native/runtime/build campaign
was reopened. This inventory is not the full distributed execution acceptance
suite and does not rename or replace its frozen helper/step names.

| Requirement | Source consumer | Authored evidence | Qualification gap |
|---|---|---|---|
| HOST-STORE-01: retained protected directory, exact lock, immutable archive and CURRENT CAS | WindowsJournalStoreV1, existing WAL/journal | Native Windows fixture spec; shared relative-path and Linux IO scenarios | Native effects and crash/fault matrix NOT_RUN |
| HOST-SERVICE-01: same capacity journal under actual signed deployment and fresh service scope | HostWindowsLocalRootV3, HostServiceDomainV3, orchestrator host-service command | CLI shape/refusal scenarios | Successful signed deployment/startup and CLI dispatch NOT_COVERED |
| HOST-QUARANTINE-01: inventory refresh after writer acquisition, retained uncertain charges | Existing host_service_reconcile_v2 through retained storage | Existing reconciliation specs remain required | Real Windows inventory drift, restart and unknown-effect cases NOT_RUN |
| HOST-CLEANUP-01: native/deployment owners survive all failures; stale copies do not affect replacement | Owner-bearing open/close turns | Native stale/lock fixture scenarios; existing owned-journal regressions | Full Host post-effect failure injection NOT_COVERED |
| HOST-CONSUME-01: newly published exact-operation consumption produces one-use native receipt | Executing-row journal wrapper + native receipt | Native receipt fixture inventory | Signed Host connection consumer belongs to parallel Windows lane |

The shared authored spec contains five scenarios: path admission/refusal,
backend-neutral CLI shape, missing-anchor/unsupported-effect refusal, immutable
Linux archive replay, and legacy WAL compare-publication behavior. These use
production functions. They do not fabricate a native Windows owner or claim
signed admission. The native spec requires real protected Windows fixtures.

Before runtime qualification, exercise: replaced/changed ancestor and DACL;
second writer within and across processes; denied read versus absent file;
failed FlushFileBuffers/rename/close and reopened CURRENT; exact and changed
consumption replay; capacity exhaustion without receipt eviction; stale close;
wrong machine/provider/policy/config/claim; stale service inventory; retained
uncertain old scope; reply encoding failure after preparation; cleanup retries;
Linux default-storage compatibility. Capture actual Windows version, filesystem,
owner/service identity and effect receipts. No benchmark result is available;
bounded inputs are source guards, not latency/RSS evidence.
