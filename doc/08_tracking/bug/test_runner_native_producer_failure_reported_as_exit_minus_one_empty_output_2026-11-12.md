# Test runner reports a failed native producer as `exit=-1, limit=infrastructure` with empty output (2026-11-12)

Status: fix-implemented-verification-pending (2026-11-27, W2-3 Windows fixes layered over 2026-11-16 owned-scope diagnostics). Not verified: end-to-end native runner route on a real Stage 2 compiler failure.

## Symptom
Four specs of `test/01_unit/lib/common/config_core` through the Stage 2-built runner (PR #8510
build at `bfe789dd411`, producer run 15 Stage 2, `--native-backend=cranelift`) all reported:

```
Error: Native backend compilation failed: cranelift (exit=-1, limit=infrastructure, budget=pass, completion=unavailable); stdout: ; stderr:
```

after 220-298 s each. The producers did not die silently: their stderr
(`<TMPDIR>/native-build-stderr-<pid>-1.log`, 505-546 KB each, under the 4 MiB
`TEST_OUTPUT_CAPTURE_BYTES`) ends with a real, classifiable verdict — three MIR failures
(`unresolved method call 'to_equal'` on the spec entry; `array return record element has no
unique provider layout: lib.common.config_core.schema::ConfigFieldDescriptor` / `layers::ConfigEntry`)
and one link failure (`undefined symbol: rt_bdd_record_result`, filed separately). The runner
surfaced none of it: exit code -1 instead of the producer's exit status, both captures empty,
limit class `infrastructure` (`native_owned_process.spl`: `scoped.process.runtime_error != 0`,
fed by `resource_scope.spl:674` `legacy_exit == -1 and not legacy_timed_out`).

## Why it matters
A reader classifies this as a host/cgroup problem and reruns; the actual MIR classes are Stage 3
risks (`unique provider layout` is the cluster that failed 2298/3066 modules in the 2026-11-07
run 15 `compiler_cli_build`). The information was produced and then dropped.

## Repro
scratch `s2runner/suite.sh k3_unit <runner> test/01_unit/lib/common/config_core` (native route env
as in `scripts/bootstrap/run-native-aot-suite.shs`, `SIMPLE_TEST_PREPROCESS_BOUNDARY=0`); compare
the runner's `Error:` line with the producer stderr file in `TMPDIR`.

## Fix & Verification 2026-11-27 (Windows host, W2-3)

- `src/lib/nogc_sync_mut/io/windows_process_owner.spl`: added `windows_process_build_command_line_v1` enforcing an explicit benign `cmd.exe` pre-switch allowlist (rejecting `/cecho`, `/d&echo`, metacharacters before `/c`/`/k`), `/S` verbatim quoting for `/c`/`/k` payloads without CRT `\"` mangling, and `_windows_cmd_join_tail_v1` / `_windows_cmd_quote_tail_arg_v1` for multi-arg `cmd.exe /c` invocations (quoting individual sub-args with whitespace/metacharacters `& | < > ^ ( ) ; ,`, preserving balanced outer quotes, rejecting unsafe embedded quotes, and wrapping with `/S` when quotes are present).
- `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`, `src/app/mcp/main_lazy_ctx_tools.spl`, `test/02_integration/hal_env/hal_env_process_spec.spl`, `test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl`, `test/fixtures/test_runner_native_process_capture/main.spl`, `resource_scope_failed_child_diagnostics_spec.spl`, and `resource_scope_child_spawn_spec.spl`: read `.usage.exit_code.value` (`i32`) for `MetricExitCode`.
- Verified (`--mode=interpreter`): `resource_scope_failed_child_diagnostics_spec.spl` 2/2 PASS, `resource_scope_child_spawn_spec.spl` 12/12 PASS (incl. live multi-arg `cmd.exe /c` via `run_in_owned_test_resource_scope`), `windows_command_owner_v2_spec.spl` 11/11 PASS, `portable_process_hal_spec.spl` 2/2 PASS, `ctx_capture_truncation_spec.spl` 4/4 PASS (`hal_env_process_spec.spl` skipped 4 POSIX cases on Windows; `simple_build_test_abnormality_detection_spec.spl` pre-existing `@manual_section` parse-error under seed).
- End-to-end Stage 2 native producer failure propagation remains pending native Linux/Stage 2 verification.
