# Signed finite host execution specification

Status: **AWAITING_VERIFICATION — NOT_RUN**. Authored manual; no generated passing evidence.

Executable: `test/03_system/app/orchestrator/feature/host_authorized_execution_spec.spl`.
Fixture: `test/fixtures/orchestration/host_authorized_execution_fixture_v2.spl`.
Design: `doc/05_design/host_authorized_execution_v2.md`.

| Requirement | Authored prevention scenario |
| --- | --- |
| HOST-EXECUTION-01/02/03 | Real journal and Ed25519-authorized packet; actual common facade enum/real adapter with explicitly scripted create/start/independent inspect; observation+signed packet readback; executing and reopened unknown replay refuse without another provider command |
| HOST-EXECUTION-01 | Corrupted actual approval signature and retained request mismatch reject before begin; engine drift may leave executing intent but refuses final native dispatch and stays charged |
| HOST-EXECUTION-02/03 | Create failure, start failure, short native identity, inspect identity mismatch and inspect failure retain charged capacity and a non-successful durable observation |
| HOST-EXECUTION-02 | Clock100/150/190 expires after create before start; no start script exists and inspected created state stays charged. Separate provider final-boundary sample190 refuses exact deadline190 while hostclock100 remains valid |
| HOST-EXECUTION-02 | Expiry before begin preserves preparation; expiry immediately after begin prevents create and persists unknown/not-attempted observation with charged execution intent |
| HOST-EXECUTION-03 | Real observation-directory obstruction returns updated owner/container and facts with recovery=true; separate creation-intent obstruction prevents start after create and retains inspected facts. Obstructions remain untouched |
| HOST-EXECUTION-01 | Two fully signed admitted operations with the same semantic request digest archive independent canonical common request/packet objects through the shared core, then expire before begin |
| HOST-EXECUTION-03 | Observation canonical/UTF-8 byte bounds and differing retained fact refusal |
| HOST-EXECUTION-03 | Bounded inspection cache permits only phase/status/reason/time updates, refuses native/create/start correlation changes and timestamp regression, and preserves original archive bytes |

| HOST-EXECUTION-02 | Valid signed clocks and archival succeed, but exact monotonic preparation deadline rejects inside begin; packet retained, journal still admitted, capacity charged, provider cursor zero |
| HOST-EXECUTION-02 | Second actual same-process journal writer refuses without replacing the existing lease; original capability remains readable/admitted and provider cursor zero |

All eleven scenarios are authored and unexecuted. Existing fixture deterministic keys are real Ed25519 test keys, not production trust roots. Engine policy observation and OCI command results are explicitly scripted simulation, not live provider evidence. Scripts assert exact routed argv and independent inspect labels; fixture memory512 bytes is intentionally small and unsuitable for live Podman.

Withdrawn historical direct-provider importer provenance: `build/host-execution-core/provenance.sdn` records original hashes for the two imported main-tree modules. Those direct-provider modules were removed after common-facade conversion; the shared core archives by operation hash with explicit fsync/readback gates.

Not tested: native image/rootless/cgroup prerequisites, real executable/engine drift, journal crash or power-loss replay, sync failures, ambiguous CURRENT publication, real transport, production authorization clocks, native wait/completion and deployment. Separate real-platform qualification plan: `doc/03_plan/sys_test/host_authorized_execution_platform.md`.

No build/test allocation was granted. Local tools were restricted with `taskset -c 0-4`; no compiler, SSpec, bootstrap, Podman or other live runtime command was executed.

Shared execution now exclusively invokes Simple Container API V2. The actual provider typed final-native deadline path is represented by the explicit provider-clock refusal regression; its implementation and dependency import still require review/verification. No Linux or Windows native authorization/platform qualification is claimed.
