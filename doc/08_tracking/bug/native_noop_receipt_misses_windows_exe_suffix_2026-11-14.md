# Native no-op receipt misses the `.exe` the Windows GNU linker wrote

Date: 2026-11-14 · Severity: P1 · Status: fix implemented, verification pending
Row: Stage 2 compiler-test matrix `test_runner_build` (slim profile),
bootstrap lane on pin `18a1f28937c2`, `x86_64-pc-windows-gnu`.

## Symptom

`test_runner_build.log` (verification/logs, 5147 lines): parse/HIR/MIR/codegen
complete, `phase=link state=succeeded done=334/334` (line 5144), then

```
error: in-process native-build: native no-op receipt publication failed: output-missing
```

(line 5146). Row `result=FAIL status=1 elapsed_seconds=8331`.

## Root cause

- The matrix passes `-o .../b4f6718e5480a13d/simple_test_runner` with no
  extension (`bootstrap-phase-verification.shs:2647`; the link command records
  `-o C:/.../simple_test_runner`).
- clang `--target=x86_64-w64-windows-gnu` writes `simple_test_runner.exe`
  (the outputs dir holds only `simple_test_runner.exe`, 2,662,400 bytes).
- `driver_orchestration.spl:407-414` then publishes the no-op receipt for
  `options.output_file` (the bare path), and
  `native_noop_publish_fault_built_v1` (`cache/native_noop_admission.spl:309`)
  fingerprints only that bare spelling -> `""` -> `"output-missing"`; the
  driver turns that into a `CodegenError`, failing a build whose link
  succeeded.
- `native_noop_admit_v1` had the same blind spot (it fingerprinted the bare
  `request.output_path`), so a receipt could never have hit either.
- Not environmental: no cache hit, no cleaned dir, no `C:/` vs `/c/` mismatch.
  Stage 3 is unaffected because `resume-stage3-from-admitted.sh` passes
  `-o .../simple.exe` explicitly.

## Fix

`native_noop_built_output_v1(path)` returns the bare path when it exists (or
already ends in `.exe`), else `<path>.exe` when that exists, else the bare
path unchanged. Publication and admission both fingerprint the resolved
spelling; the receipt still records `request.output_path`, so identity is
unchanged. Spec:
`test/01_unit/compiler/driver/native_noop_windows_exe_output_spec.spl`.

Verification needs a new Stage 2 built from source carrying the fix: the
failing code runs inside the admitted Stage 2 binary, so rerunning the gate
against the Stage 2 built from `18a1f28937c2` fails the same way.

The matrix's own artifact check (`bootstrap-phase-verification.shs:1224`,
`[ ! -e "$expected_executable" ]` on the bare path) already passes under Git
Bash: MSYS `stat` resolves `simple_test_runner` to `simple_test_runner.exe`
(checked against the retained outputs dir). So once the driver stops failing,
nothing else in the row rejects the `.exe` spelling.
