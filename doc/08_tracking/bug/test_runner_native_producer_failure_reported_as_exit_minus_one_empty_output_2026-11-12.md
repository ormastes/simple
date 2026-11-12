# Test runner reports a failed native producer as `exit=-1, limit=infrastructure` with empty output (2026-11-12)

Status: OPEN (filed, not fixed). Severity P2 (every native-route failure looks like an
infrastructure kill; the real compiler error is only in a file nobody is told about).

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

## Next
Find why the owned-process scope returns `legacy_exit == -1` with empty captures for a child that
exited non-zero after writing ~0.5 MB to stderr (pipe/capture path of
`run_in_owned_test_resource_scope`), and make the runner print the tail of the producer's
diagnostics file on any native compile failure.
