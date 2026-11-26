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

- `src/lib/nogc_sync_mut/io/windows_process_owner.spl`: keep unquoted leading `cmd.exe` switches prior to `/c`/`/k` so `cmd.exe` does not treat a closing quote on `"/c"` as the command string opener.
- `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`: pass `scoped.process.usage.exit_code.value` (`i32`) rather than `MetricExitCode` into `make_result_from_output` and `apply_hosted_lane_child_error`.
- Updated `resource_scope_failed_child_diagnostics_spec.spl` and `resource_scope_child_spawn_spec.spl` to read `.exit_code.value`.
- Verified (`--mode=interpreter`): `resource_scope_failed_child_diagnostics_spec.spl` 2/2 PASS, `resource_scope_child_spawn_spec.spl` 10/10 PASS, `windows_command_owner_v2_spec.spl` 10/10 PASS, `wa_src_lane7_scoped_child_projection_spec.spl` 3/3 PASS, `executor_lanes_split_spec.spl` 3/3 PASS. Note `test_runner_bounded_output_contract_spec.spl` has 11/14 pre-existing Windows shell-quoting / moved-facade source-text assertion failures unrelated to these edits.
- End-to-end Stage 2 native producer failure propagation remains pending native Linux/Stage 2 verification.
