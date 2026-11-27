# native-build: final (link) worker dies with 0xC0000142 after fully successful codegen; ~4.5 h of work lost

Status: FIXED (transient retry + status label + manual link recovery guidance implemented; automatic per-module object reuse remains a separate enhancement).

## Symptom
After a fully successful Cranelift codegen
(`[mir-shard] completed_workers=2 failed_workers=0 failed_modules=0`) the parent printed

    error: native-build worker exited with code -1073741502.
    interpreter: c:/dev/p3diag/p2.exe (exit code -1073741502)

and produced no binary. -1073741502 = 0xC0000142 = STATUS_DLL_INIT_FAILED: the final
(link) worker process could not initialise.

## Source location
The message is printed in `src/app/cli/native_build_main.spl:2615`
(`stderr_write("error: native-build worker exited with code {code}.\n")`, inside the
`if code != 0:` branch). The branch prints the last diagnostic line and relays stderr; it
does not retry and does not print the link command or response-file path.

## Context / hypotheses (neither confirmed)
Free RAM was < 1 GB and the build's parent console/wrapper shell had been killed by the
host's low-memory reaper hours earlier. Hypotheses: (a) desktop-heap / console loss for a
child spawned after the console owner died; (b) memory exhaustion at process start.

## Consequence
~4.5 h of compile work has no artifact: per-module objects are not reused by the next
run (`cached=0`), so a failed final step means a full rebuild.

## Workaround used
Hand link of the 1,429 `build/aot-*.o` objects with a replica of the driver's link recipe:
clang --target=x86_64-w64-windows-gnu, runtime C sources compiled fresh, plus a generated
entry stub calling every `__module_init*`. The binary links and answers `--version`.

## Proposed fixes
1. Retry the final worker spawn on 0xC0000142 (transient environment failure, not a
   build defect).
2. Persist and reuse per-module objects so a failed final step can be resumed.
3. On failure print the link command / rsp path so a hand link need not be reverse-engineered.

## Does current source fix it?
Yes (for transient retry and manual link recovery, items 1 and 3 above; automatic cross-invocation `aot-*.o` reuse in item 2 remains separate):
- `src/app/cli/native_build_exit_status.spl`: added `native_build_is_dll_init_failed_v1(code)` for `-1073741502` / `3221225794` (`0xC0000142`), and updated `native_build_windows_status_label` to return `"0xC0000142 (STATUS_DLL_INIT_FAILED)"` for both forms.
- `src/app/cli/native_build_main.spl`: added `native_build_should_retry_dll_init_v1` and `native_build_dll_init_retry_delay_ms_v1`, retrying the final (non-shard) worker up to 2 times (`1000ms`, `2000ms`) via `sleep_ms` with `stderr_write` warnings when it exits with `0xC0000142` and no valid output artifact; added `native_build_dll_init_recovery_lines_v1` and `native_build_worker_failure_lines_for_output_v1` (preserving `native_build_worker_failure_lines_v1`) to print explicit recovery hints naming `{output_path}.link-command.txt`, surviving `aot-*.o` objects, and `scripts/bootstrap/p3-manual-link-stage3.shs`.
- `test/01_unit/app/cli/native_build_dll_init_retry_spec.spl`: unit coverage for status classification, retry gate, backoff delays, and recovery guidance.
