# V5 primary-service refusal test plan

Status: AUTHORED_NOT_RUN. Scope is the real command boundary before Host domain
opening. No native execution or successful service startup is simulated.

| Requirement | Executable evidence | Coverage limit |
| --- | --- | --- |
| HOST-01 | Six scenarios in `test/03_system/app/orchestrator/feature/host_primary_service_v5_refusal_spec.spl` | Argument rejection and syntax/authority distinction only; enrollment and usable capabilities remain unqualified. |
| CTR-02 | Unknown backend, unsupported direct-provider route and canonical endpoint refusal | No actual engine command or exact runtime cleanup evidence. |

Manual: `doc/06_spec/03_system/app/orchestrator/feature/host_primary_service_v5_refusal_spec.md`.

Integrate the actual V5 app/Host/smux source closure first. Compile and execute
with an admitted self-hosted Simple producer under the existing CPU/resource
limits. Missing producer or dependency is BLOCKED, never a skipped pass. Do not
restart a closed native/bootstrap campaign to run this suite without its
required authorization. Check actual case execution and exit status; source
loading alone is not execution. Generate the mirrored manual with repository
SPipe docgen when that tool is admitted; the authored manual is not generated
evidence. The expected case count is six.

The positive Windows fixture and native procedures remain in
`doc/06_spec/03_system/app/orchestrator/feature/windows_primary_service_v5_acceptance.md`.
This bounded refusal suite does not replace that acceptance gate or the
distributed orchestrator's full requirements.
