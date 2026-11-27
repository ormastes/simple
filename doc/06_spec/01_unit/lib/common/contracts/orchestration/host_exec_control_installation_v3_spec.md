# Pure exec-control installation codec — authored specification

Status: **NOT_RUN / AWAITING_VERIFICATION**. Authored manual; no generated execution evidence, compiler/build/test invocation or native policy observation. Local editing/static processes used shared CPU affinity 0–4.

Requirement: HOST-EXEC-CONTROL-INSTALL-01. Source: `test/01_unit/lib/common/contracts/orchestration/host_exec_control_installation_v3_spec.spl`.

| Case | Exact `step()` text |
| --- | --- |
| 1 | roundtrips exact raw canonical policy and full opaque signed request bytes |
| 2 | validates standalone shared envelope shape and exact original operation correlation |
| 3 | rejects nonobject noncanonical wronghash unknown missing and oversized inputs |
| 4 | validates historical scope structurally without claiming current epoch or authentication |

The four source cases exercise exact canonical intent/request roundtrip, full raw control-policy hash binding, standalone common envelope shape, action/id/host/environment/payload correlation, strict canonical object policy, malformed/unknown/missing/UTF8 byte limits and historical scope structure. Shared signed proof bytes are **opaque codec data** here: altered request metadata is not represented as cryptographically authenticated. Actual owner verification belongs to the separate signed installation consumer.

This pure checkpoint provides no installed root, current service epoch, native policy schema, readiness, journal admission, exec capability, allocation or child delegation. Scope structure accepts historical epochs without comparing an invented current clock/scope. Actual loader/current owner must check current pins. All four cases and platform/build qualification remain NOT_RUN; the actual owner/public route/source fault specs continue separately and are not complete at this codec checkpoint.
