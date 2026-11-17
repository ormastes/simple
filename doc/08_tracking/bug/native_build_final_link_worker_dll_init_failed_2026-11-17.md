# native-build: final (link) worker dies with 0xC0000142 after fully successful codegen; ~4.5 h of work lost

Status: OPEN. Cause unconfirmed.

## Symptom
After a fully successful Cranelift codegen
(`[mir-shard] completed_workers=2 failed_workers=0 failed_modules=0`) the parent printed

    error: native-build worker exited with code -1073741502.
    interpreter: c:/dev/p3diag/p2.exe (exit code -1073741502)

and produced no binary. -1073741502 = 0xC0000142 = STATUS_DLL_INIT_FAILED: the final
(link) worker process could not initialise.

## Source location
The message is printed in `src/app/cli/native_build_main.spl:2587`
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
No. `native_build_main.spl:2587` on origin/release/1.0.0 is a plain report with no retry
for this exit code (read, not executed).
