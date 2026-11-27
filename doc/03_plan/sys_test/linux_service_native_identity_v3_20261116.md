# Native service identity evidence plan — fixture P2 successor

Status: AUTHORED_NOT_RUN; source review pending. One fixture-only successor to immutable identity6 cycle8 R1; production and native26/Source6/stats remain unchanged. Cumulative cycles7–9 are not reset.

Modern registration: describe + **3 it "should ..." cases**, visible step flows and canonical matchers. These are SOURCE case counts, not binary-owned discovered/executed counts. Missing actual setup fails then returns before further effects. Acceptance matrix HOST03/04 receives identity support only.

| Requirement / finding | Actual case / oracle | Status |
|---|---|---|
| IDENTITY-001 / 002 | Seven fields compared to genuine independent reader/epoch/native observations; copied/new borrow refuses closed original reader while successor stays current | AUTHORED_NOT_RUN |
| IDENTITY-002 | Original successor closes; real separate reader stays current; old/new borrow refuses | AUTHORED_NOT_RUN |
| IDENTITY-FIXTURE-P2-01 | Live real original pair; same pre-open guard returns exact prior-pair-unresolved error before another factory; saved actual partner observations remain current | AUTHORED_NOT_RUN |
| IDENTITY-FIXTURE-P2-01 uncertain-close branch | Returned typed owners retained; first diagnostic sticky; all later pair_open calls refuse before factory/transition; consumed-error never retried or stale promoted to release | Source correction; actual native pending/consumed-close fault NOT_COVERED |
| IDENTITY-003 | Unchanged production leaf has no native allocation/registry/writer/close/getter; upper/Host own original lifecycle and service incarnation separately | Prior production scoped SOURCE_PASS; whole signing NOT_COVERED |

Executable: test/03_system/tools/linux_service_native_identity_v3_spec.spl. Mirror: doc/06_spec/03_system/tools/linux_service_native_identity_v3_spec.md. Three primary flows are visible; exact executable is folded below. Future capture: actual compiler/native logs and cleanup diagnostics; no fabricated capture currently exists. Three supporting cases do not claim complete per-requirement branch coverage.

Fixture scalars are isolation bookkeeping, never capability evidence or a new registry. Existing typed arrays retain all actual owners before status checks and returned pending owners before diagnostics. Closed aliases remain retained, so array size is not availability evidence. A setup is unresolved before its first acquisition; only both original positive closes with no sticky diagnostic reopen the gate. Setup failures and unexpected early returns leave it closed. No after_each reset/blind retry erases custody.

Actual administrator provisioning is required and NOT_PERFORMED: dedicated UID, protected installed profiles/stores and real manager/cgroup topology. Ordinary shell/default Podman is not equivalent. Missing provision fails, never skips. Pending-close injection, fork/namespace/profile replacement and whole signing/incarnation lifecycle remain NOT_COVERED.

Root prohibits compiler/test/native launches in this source cycle. The system_test skill's docgen, binary case inventory and compiled execution therefore remain NOT_RUN, required gates rather than inferred passes. Manual is authored, not generated. No new framework is introduced.
