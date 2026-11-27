# Container control deadline contract

Status: **AWAITING_VERIFICATION — NOT_RUN**. Authored manual, not generated execution evidence.

Production: `src/lib/common/contracts/container/control_deadline_v1.spl`.
Executable: `test/01_unit/lib/common/contracts/container/control_deadline_v1_spec.spl`.

`ContainerControlDeadlineV1` binds semantic request digest, ORIGINAL workload operation ID, explicit stop/destroy action set and positive Unix-millisecond expiry. `container_control_deadline_v1` accepts1..2 unique control actions only. `container_control_remaining_ms_v1` revalidates public values and exact request/operation/action, requires positive actual time strictly before expiry, and returns bounded remaining admission milliseconds. It performs no native action, signature verification, kill, cleanup or capacity release.

CONTAINER-CONTROL-DEADLINE-01: authored cases bind original workload identity; reject malformed digest/operation/expiry, unsupported/duplicate/excessive actions, changed request or separate cleanup ID, and actions outside the granted subset.

CONTAINER-CONTROL-DEADLINE-02: authored cases reject zero/negative clocks and exact expiry, revalidate forged/mutated public structs, and check safe arithmetic up to the signed integer limit. Seven cases total; all unexecuted.

Trusted cleanup consumers must verify fresh separately signed `host_cleanup_v1` grant+approval against the original workload envelope/ID/payload and derive the minimum verified expiry. Providers sample their actual clock at the final native control boundary. This data value is not authorization by itself. Expiry must never automatically kill a workload or release any ledger charge. Cleanup wait/evidence/absence and same-journal release are separate mechanisms, not implemented by this pure type.

No compiler, SSpec, build or provider command ran. Source handoff only; local tooling used `taskset -c 0-4`.
