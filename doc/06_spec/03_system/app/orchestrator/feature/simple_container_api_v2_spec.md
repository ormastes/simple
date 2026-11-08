# Actual Simple Container API V2 route guards

Status: **NOT_RUN — awaiting verification**. Authored manual; no native runtime
PASS or generated evidence. Authored labels ORCH-02/HOST-02 record intended
identity/owner/scope assertions pending existing requirement reconciliation.

Spec: `test/03_system/app/orchestrator/feature/simple_container_api_v2_spec.spl`.
Fixture: `test/fixtures/orchestrator_acceptance/simple_container_api_v2.spl`.

## Setup: actual platform owners, never fake fallback

The unsupported-backend scenario deliberately needs no provider: reject unknown
backend before policy is read or state is opened. The other scenarios MUST use
real configured API-opened Linux Podman or Windows Docker process owners. No
nullable/fake provider is constructed and unavailable cases never skip-pass.

Native host case files, produced by platform acceptance setup, are required at
`build/simple-container-api/linux-case.sdn` and `windows-case.sdn`. Each contains
backend, policyPath, requestPath, stateRoot and providerIdentityDigest. The policy
must be actual platform policy; requestPath holds a canonical common request with
real backend body and matching native scope. The identity pin is administrator
provided, not automatic trust in discovery. No placeholder case is committed.

The fixture reads bounded case/policy/request files, calls actual API observe,
checks real native machine/boot/provider pin, opens through API, then constructs
a correctly bound future launch deadline from the actual native clock. Physical
host ID remains an authorized alias and need not equal native machine identity.

Current native-only open rejects weak machine-boot counters and service mode.
The diagnosed Windows weak-boot path is BLOCKED until persistent service owner/
quarantine exists; it cannot qualify this native-incarnation scenario by filling
boot_id with a counter. Host-appropriate execution and full platform coverage
must remain explicit; missing runtime is not a successful test result.

## Scenarios and checks

1. Refuse unsupported backend with the exact API error before policy/state use.
2. For the real Linux case, project the request through actual leaf validation.
   Refuse unknown action, wrong backend, changed native boot, native machine and
   physical alias. Refuse create through read and wrong-scope read/recovery.
   Check returned owner still projects the original digest/CPU/memory.
3. Perform the same public API route checks for actual Windows Docker process
   owner when its native continuity prerequisite is available.

The shared `simple_container_api_route_checks_v2(owner,request,deadline)` accepts
an already opened real owner so platform lifecycle fixtures can run the same
checks between real operations. Rejected recovery uses a wrong operation ID;
it is not a fabricated successful intent or native observation.

## What these assertions do and do not prove

ORCH-02 maps to exact dispatch routing and retained owner on refusal. HOST-02 maps
to semantic projection and full owner/request scope checks before mutating leaf
calls. Unchanged projection is not an independent provider-absence oracle.

Actual source dispatch invokes leaf apply/read/recover/intent; these tests do not
replace each platform owner's full prepare/create/start/inspect/logs/wait/stop/
destroy/recover nonce/native-identity acceptance through the SAME API. Reads have
no launch deadline; expiry must not kill workloads or prohibit inspection.

The separate test-only scripted Linux wrapper requires a real adapter reporting
is_scripted_fixture_v2(); production never selects it as fallback, and scripted
assertions never count as native Podman/Docker execution. Parallel deadline/leaf
sources are still prerequisites. No builds, admitted SSpec, native lifecycle,
coverage, SPipe docgen/maintenance or full-runtime qualification was performed.
