# Windows Job Object Resource Receipt

Status: blocked pending a prepared Windows qualification host.

Owner: runtime/process provider maintainer.

Current source boundary: `src/runtime/runtime_process_owned.c` returns `ENOTSUP` from the observed owned-process ABI on `_WIN32`; `src/runtime/runtime_process.c` already owns the established Job Object launch/kill lifecycle. `resource_scope.spl` therefore executes through the legacy bounded facade and reports `ResourceEvidenceQuality.Unavailable` rather than fabricating parity.

Unblock work:

1. Extend the versioned owned-process start contract with explicit memory, CPU, PID, and descriptor quantities.
2. Apply `JOB_OBJECT_LIMIT_PROCESS_MEMORY`/`JOB_OBJECT_LIMIT_JOB_MEMORY`, active-process, and CPU limits before resuming the child.
3. Collect `JOBOBJECT_BASIC_ACCOUNTING_INFORMATION`, `JOBOBJECT_EXTENDED_LIMIT_INFORMATION`, and limit-violation notifications into the common receipt.
4. Run direct-child, descendant, memory-limit, process-limit, timeout, and external-cancel fixtures on Windows.
5. Preserve the current unavailable fallback until all receipt fields are proven.

Resume command on the Windows host: build the source-matched runtime and run the retained abnormality system spec through `bin\\simple.exe test test\\03_system\\app\\perf\\feature\\simple_build_test_abnormality_detection_spec.spl`.
