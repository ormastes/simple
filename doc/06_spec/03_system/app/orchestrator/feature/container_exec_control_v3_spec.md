# Finite actual exec-control probe route

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 exact retained parent; HOST-02 owner-preserving observations.
Spec: `test/03_system/app/orchestrator/feature/container_exec_control_v3_spec.spl`.

Setup: pure metadata cases construct exact-shaped parent plan/runtime and distinct
parent/control/policy/hash values. Actual common preflight cases use existing
real scripted leaf adapters, not a fake common owner or native-success response.
They intentionally fail BEFORE the native probe: malformed input, unsupported
backend or explicit scripted-observer prohibition. No installed peer, native
parent inspect, signature, factory readiness or actual control success is faked.

| Exact step | Procedure / checks |
|---|---|
| matches exact constructed parent and separate parent control policy identities only as data | Match complete constructed Linux and Windows metadata with explicit API profiles; reject Windows with Linux API version. Retain separate parent baseline and composite control identity without calling it native proof. |
| refuses every changed parent runtime field and request digest | Independently change each of7runtime fields and request digest; refuse each. |
| refuses wrong scope baseline policy API clock and malformed observation hashes | Refuse scope alias/machine, parent baseline, policy, unsupported API/backend, unavailable clock and malformed control/query/evidence hashes. |
| calls actual common probe and refuses invalid input before native or scripted execution | Call actual common function with invalid timeout or malformed policy; preserve owner, no observation/cleanup and zero scripted executor calls. |
| refuses scripted native observation even with canonical installed policy and exact parent | Use canonical actual installed-policy codec with an exact-shaped scripted parent; actual common route refuses scripted observation before native probe or inspect. |
| refuses actual Windows tagged owner without fabricating a Linux socket observation | Pass actual Windows scripted tagged owner; refuse unsupported observer while retaining original scope and no synthetic socket observation. |

Actual positive source path (NOT executed): validate bounds/backend and canonical
parent/runtime, common project/semantic request validation, cached Linux backend/
executionOS/native-machine correlation, protected installed-policy decoding, then
actual linux_oci_installed_probe_v3. Any error or retained Unix connection returns
no observation and preserves cleanup; even impossible success-with-cleanup stops
before inspect. Successful actual probe must have CLI identity equal cached parent
provider baseline. Actual simple_container_read_v2(owner,"inspect",request) then
returns the updated owner; require running, successful operation and exact all7
runtime fields. Query/evidence hashes aggregate BOTH actual installed-service and
actual inspect command/operation hashes, plus scope/request/CID/control identity.
Actual Unix time is sampled after parent correlation. Metadata validation finishes
before observation is exposed. Restored or supplied data provides no authority.

Installed policy bytes are TRUSTED installed host configuration, not packet wire.
Linux explicitly supports installed API5.2.5. Metadata also recognizes Windows
Docker API1.48; the effectful common route refuses Windows until its actual
pending-owner adapter is integrated. The supplied timeout selects an installed
probe admission/publication window of at most30s, not a hard return-time bound:
executable hashing or capture-slot acquisition can outlast it and then refuse.
Parent inspect retains its existing admitted owner/request timeout. No overall
single-time-budget or async readiness claim is made. Cleanup helper calls actual
leaf close once and retains any connection/error, including error after consumed
owner; no fabricated success or retry. Live Host child begin, signed authority,
Windows observation and native-positive platform qualification remain required.
Dependencies from the actual Podman engine-exec owner are referenced only, never
copied. Builds/tests were prohibited for this task.
