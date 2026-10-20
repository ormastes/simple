# rc1 packages the bootstrap CLI as simple; specs fail at smf compile

Canonical ID: `rc1_packaged_simple_is_bootstrap_cli_specs_fail_smf_compile_2026_10_20`

Status: OPEN. Accepted in the release.yml smoke step as a known degradation.
Bug database registration is pending reconciliation.

## Failure

The release.yml `build-bootstrap` rows linux-x86_64 and windows-x86_64 package
stage1 as `bin/simple-runtime` (Linux, behind the `bin/simple` wrapper) and as
`bin/simple.exe` (Windows). Stage1 is built from
`src/app/cli/bootstrap_main.spl`, the bootstrap CLI, which only exposes
`compile` and `native-build`. No full CLI (`src/app/cli/_CliMain/main_and_help.spl`)
is built or packaged.

`bin/simple_test_runner` runs a spec through `SIMPLE_BINARY`. Against that
binary, every spec fails at SMF compile:

```
SPEC FILE VERDICT: test/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 ... degraded=smf-compile-error:error:_bootstrap_compile_supports_--format=smf_only
```

Evidence: run 39362039541, jobs 118430432407 (linux-x86_64) and 118430432384
(windows-x86_64).

## Accepted degradation

The smoke step runs `simple --version`, then runs the test runner on one spec.
It accepts a non-zero runner exit only when the verdict line has `executed=1 `
and the exact signature above. Any other failure fails the step.

## Fix

Build and package the full CLI, as the canonical phase-4 bootstrap does
(`bin/simple` from `src/app/cli/_CliMain/main_and_help.spl`). Then drop the
accepted signature from the smoke step so the spec has to pass.
