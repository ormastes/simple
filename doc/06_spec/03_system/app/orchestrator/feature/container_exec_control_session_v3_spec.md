# Actual Windows control session common adapter

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 exact retained parent/control association; HOST-02 live owner retention.
Spec: `test/03_system/app/orchestrator/feature/container_exec_control_session_v3_spec.spl`.

Setup: use actual common begin and existing real scripted Linux/Windows leaf
owners. Expected Windows parent uses its full runtime shape and opaque scope
fence. Tests intentionally exercise only preflight refusal and never construct
WindowsDockerExecControlProbeV3, native pipe, positive session or actual observation.
Supplied bounded bytes for scripted-owner refusal are explicitly not interpreted
as installed policy or claimed canonical installed configuration.

| Exact step | Procedure / checks |
|---|---|
| refuses empty or overbound installed policy while retaining the actual owner | Actual begin refuses empty/over1MiB policy input, returns original owner scope, no session/observation and zero consumed script commands. |
| refuses Linux without fabricating an asynchronous session or fallback | Actual Linux owner returns explicit finite-route-required error without an async session/fallback. |
| refuses mismatched exact parent before the adapter can open a native exchange | Actual begin refuses mismatched UID/attempt/operation/generation/engine/fence or malformed native ID before adapter/native probe; no scripted commands run. |
| rejects scripted observation before actual adapter begin and preserves backend scope and baseline | Exact-shaped Windows parent with scripted owner reaches explicit scripted-observer-forbidden guard before adapter begin. Retain backend/scope/baseline; no native call or readiness claim. |

Actual positive source path is NOT executed: begin validates common backend,
full scope, cached baseline/platform, semantic project and exact parent. It then
calls actual adapter.begin_exec_control_probe_v3. The actual adapter canonical
installed-policy decoder precedes owner creation, so SHA256 of input binds exact
installed bytes. Adapter also verifies retained own CID and fresh host state.
Its _fresh uses the existing bounded synchronous observer before Engine polling;
this is NOT a whole-host nonblocking or async-readiness claim.

Every actual Pending/Complete/Closed/CleanupRequired outcome wraps its native
probe owner. Complete uses actual observation_v3 and common matcher against the
original request/runtime/provider/policy, retains the probe for real stream
planning and exposes observation only on success. Rejected before begin has no
owner; unexpected later Rejected retains original session. Errors expose no
observation. Poll requires current full scope/baseline/project correlation before
advancing and returns original session on mismatch.

Collect deliberately needs NO fresh parent/project/scope/provider admission:
the parent may exit or epoch change while read-only connection cleanup remains
owed. It advances only the retained native probe, preserves passed container owner
unchanged and never emits an observation. Closed drops session ONLY when actual
has_owned_exchange_v3 is false; otherwise cleanup remains. Unexpected Complete or
Pending during collect is retained as unconfirmed cleanup, never readiness.
No fake owner seam tests these native cleanup states; they remain source-review
and real platform test obligations. Linux remains the existing separate finite
route until actual reserved async ownership exists. Windows dependency is immutable
159eb961e38fc4a5bf1b8f7182433d408f56a381, referenced without copying. Host child begin,
signature/lease admission and native-positive routing remain required. No builds,
tests, guards or repeated checks were run for this task.
