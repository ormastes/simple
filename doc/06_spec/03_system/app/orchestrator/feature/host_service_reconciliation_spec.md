# Host service startup reconciliation specification

Status: **AWAITING_VERIFICATION — NOT_RUN**. Authored manual, not generated evidence.

Executable: `test/03_system/app/orchestrator/feature/host_service_reconciliation_spec.spl`.
Fixture: `test/fixtures/orchestration/host_service_reconciliation_fixture_v2.spl`.
Production under review: `src/lib/nogc_sync_mut/orchestration/host_service_reconciliation_v2.spl` (parent-owned, unchanged by this worker).

| Requirement | Authored actual-code case |
| --- | --- |
| HOST-RECONCILIATION-01 | Empty real journal remains quarantined until actual common service refresh, receipt readback/private mode and typed quarantine completion. Returned receipt correlates actual journal revision/sequence and complete inventory digest. |
| HOST-RECONCILIATION-02 | An absent admitted row becomes exact cancelled/no-effect release. Three historical released rows total6000cpu/1.5GiB above4000cpu/1GiB; quarantined open still reaches reconciliation, proves those releases and enables full capacity. A genuinely stale pre-cancellation writer copy refuses before another inventory/admission. |
| HOST-RECONCILIATION-02 | Prior begin becomes outcome-unknown on real reopen. Empty inventory never frees it. At normal capacity it stays charged while unused capacity becomes available; after capacity downsizing below its charge, admission remains blocked and actual common create returns quarantine-pending without consuming a script. |
| HOST-RECONCILIATION-02 | Exact old-incarnation inventory matches retained intent/common plan and stays charged/uncertain; current-incarnation readiness does not adopt its old epoch or release resources. |
| HOST-RECONCILIATION-03 | Factory-empty/fresh-unaccounted native object proves current inventory is used; admitted row with native effect but no committed begin, changed retained request digest and excessive native charge each refuse before receipt/readiness. |
| HOST-RECONCILIATION-01/03 | Factory snapshot cannot ACK readiness. A separately successful refresh followed by the host's mandatory refresh failure clears the actual adapter's freshness gate; stale ACK then refuses even though its former digest was valid. |

The fixture uses the ACTUAL Windows `scripted_service_fixture_v2` through `windows_adapter_owner_fixture_v2` and the approved common enum wrapper. Sample0 is consumed by construction; each actual refresh consumes the next sample. No caller-supplied ready boolean, fake common owner or native-observation fallback is used. These are synthetic Windows inventory facts and explicitly scripted adapter observations, not Windows/Docker/native qualification. Empty native command scripts remain unconsumed throughout the eight cases.

The publication-fault case obstructs the real receipt directory after the journal writer is acquired. Cancellation advances the actual journal, publication fails, and the returned owner remains quarantined. Removing only that obstruction and retrying the same live owner requires another actual inventory refresh; the receipt filename hashes its full canonical bytes and the ACK matches the updated journal commit. Historical receipts are not overwritten or selected as readiness authority.

The existing-receipt permission case supplies exact canonical empty-turn bytes with mode0644 and a separate interrupted private stage. The real owner refuses admission without repairing the destination. Only after explicit fixture administrator repair to0600 does a fresh inventory/validation turn admit; original receipt bytes and interrupted-stage evidence remain unchanged. Atomic staging prevents new partial writes from poisoning the final receipt name. All cases remain NOT_RUN.

Completed release continuation consumes the same `host_capacity_completion_evidence_v1` validator used by normal settlement and forced quarantine reopen. `host_cleanup_spec.spl` now creates real signed cleanup plus actual scripted native absence, reopens the actual journal quarantined and verifies release; tampered and missing proof instead remain charged. Startup additionally requires no current inventory object before selecting `released-completion-evidence`. This cross-spec source coverage is NOT_RUN; no flag-only or inventory-absence-only release is permitted.

Historical reservations are created/begun/aborted using the real capacity owner and existing V2 journal, then closed/reopened through `host_capacity_owner_open_quarantined_v2` with a fresh service-incarnation fence. Historical request bodies are explicitly canonical reconciliation metadata, NOT runnable Windows requests or previous native execution evidence. The current host's request/charge/plan matching and readiness mechanisms are the actual production code. Native query truth and previously signed platform admissions remain outside this fixture.

Regression1ed590 is exercised without pretending overcapacity is allocatable: the quarantined history projection returns continuity=false and `host_available_capacity_v1` still reports capacity-exceeded before reconciliation. Only proven process-crash no-effect rows are released. Unknown overcapacity remains charged, continuity=false and provider-quarantined; empty inventory alone is not absence authority.

The tested durability profile is explicitly `process-crash-v1`. Object publication/readback/sync paths and journal metadata are asserted in authored code, but no runtime was executed and no power-loss-safe admission is claimed. Shared WAL/barrier qualification, process crash injection, actual Windows inventory completeness, native provider drift, persistent root/IPC ownership, service enrollment signatures, terminal-result persistence, native absence/storage proof and platform cleanup remain separate unexecuted gates.

Read-only dependency references: Windows fixture commit48b2faa3f272c0f45ac9076107c9a293cbfd8128 at `/home/yoon/dev/simple-windows-docker`; approved common Windows wrapper0e512 and shared contracts from the architecture lane. No dependency source was copied. No compiler, SSpec, build, Podman, Docker or native helper command ran. Local tooling used `taskset -c 0-4` under the shared five-CPU limit.
