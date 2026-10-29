# Compare Hello and BuildRunner stages

Add `--trace-stages` to `hello-sanity-matrix.py` or `buildrunner run` when diagnosing where a build stops. The option is off by default. It changes diagnostics, not task admission, process containment, result acceptance, or compiler selection.

```sh
python3 scripts/bootstrap/hello-sanity-matrix.py --trace-stages \
  --compiler /path/to/pinned/simple --phase 2 --compile-route positional \
  --backend llvm --source-root /path/to/source --runtime-path /path/to/runtime \
  --output /path/to/new-evidence

buildrunner run --trace-stages --manifest job.sdn --state /existing/private/state \
  --source-root /canonical/source --output-root /existing/private/published
```

The Hello matrix writes `<command>.trace-begin.sdn` before process launch and `<command>.trace-end.sdn` after the command returns. These records contain phase, backend, compilation route, compiler SHA-256, command stage and exit code. Existing per-command stdout/stderr and resource receipts remain authoritative for their respective evidence. A missing end record identifies an incomplete command; an exit code of zero does not replace artifact validation or manager verification.

For compiler commands, the matrix explicitly applies these settings after inherited `SIMPLE_*` settings are sanitized: `SIMPLE_BOOTSTRAP_DIAG=1`, `SIMPLE_COMPILER_PHASE_PROFILE=1`, `SIMPLE_COMPILER_TRACE=1`, `SIMPLE_KEEP_LLVM_IR=0`, and `SIMPLE_MEM_SNAPSHOT=0`. Compiler diagnostics stay in the existing bounded stdout/stderr logs. Executing the generated Hello does not receive these added settings.

When the matrix uses its BuildRunner provider, it forwards `--trace-stages` to both the manager and the managed Hello driver. The managed driver enables the same compiler diagnostics after its own environment sanitization. This preserves the task's pinned environment boundary: the canonical BuildRunner flag alone does not alter compiler environment or task identity.

BuildRunner writes `build_trace` SDN records to stdout for root/source/database admission, scheduler startup, task admission, cache reuse, dispatch, worker memory/V4 admission, executable pinning, V4 ownership transfer, collection, publication, and terminal results. Local and SSH worker invocations receive the option. Standalone Linux and Windows workers emit input-admission, process-start and result events; Linux additionally marks delegated capacity admission. Their `process-start` owned event follows acquisition of the native owner lease. Worker records include the task identity, producer SHA-256, attempt, and recognized backend/route. A managed Hello task's producer can be Python; the matrix records separately identify the actual phase compiler. `unspecified` means the task arguments did not establish a recognized backend or route.

The new structured trace does not copy argv, paths, environment values, or arbitrary error messages. Existing human-readable errors and compiler logs are unchanged. Trace events are diagnostic only; a `v4-capabilities` begin followed by worker result exit 2 does not prove that a compiler started. Only `v4-start` with `event: "owned"` indicates that the worker received an active process lease. No trace option bypasses the V4 admission guard.
