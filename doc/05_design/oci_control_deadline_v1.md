# Explicit stop/destroy control admission

Status: AUTHORED / UNEXECUTED. No native acceptance or runtime timing result is claimed.

`ContainerControlDeadlineV1` is separate from launch authority. It binds canonical workload request digest, original workload operation ID, allowed stop/destroy actions and absolute admission expiry. The Linux adapter's `control` method accepts only stop/destroy, verifies the real canonical common request and managed policy, bounds operation duration using the existing duration policy, then passes the context as an optional argument through the leaf method into `_execute`. No mutable control field or setter exists.

Controlled stop/destroy validate request/action/operation against a trusted current clock at entry, before even cached idempotent receipts. The executor repeats this after current engine-policy observation and absolute argv preparation. Expiry or a failed clock refuses the requested operation; no timer automatically kills a container or releases ownership/budget. Legacy nil-context stop/destroy and the existing `apply` path retain their previous behavior, independently of any expired launch grant.

Live controlled commands reuse `process_run_bounded_admitted_v1` with the control expiry, preserving structured timeout/output saturation handling. This existing native capture owner waits for its governor slot and rechecks admission before fork/exec. The absolute expiry is an admission boundary, never a cap on the running cleanup command's duration; ordinary operation timeout stays unchanged. There is no new FFI or raw process call.

The common consumer is `simple_container_control_v2`; its source and the pure control contract/helpers are separate orchestration/Host prerequisites. Seven focused authored scenarios cover actual common dispatch and exact routed argv, independent entry/final clock samples, expiry crossing observation, invalid binding/action, missing clocks, cached success refusal, policy drift and unchanged legacy cleanup. They remain UNEXECUTED. Scripted assertions do not qualify the actual native pre-exec boundary.
