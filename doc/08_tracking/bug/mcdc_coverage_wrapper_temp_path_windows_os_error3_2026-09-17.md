# MC/DC coverage wrapper staging broken on Windows — every spec degraded to plain interpreter

- **Filed/fixed:** 2026-09-17
- **Status:** FIXED — verified on Windows 11 with the seed interpreter
  (`api_registry_spec.spl --coverage`: 5/5, no `mcdc-fallback` lines).

## Symptom

Every spec under `simple test --mode=interpreter` (coverage lane) printed:

```
[mcdc-fallback] <spec>: MC/DC instrumentation skipped: spec failed to compile to
standalone SMF; degraded to plain interpreter ... io: Cannot read
"...\Temp/simple_cov_test\01_unit\...\<name>_spec_spec.spl":
The system cannot find the path specified. (os error 3)
```

Coverage/MC-DC evidence was silently lost for the whole run; pass/fail still
reported from the plain interpreter fallback.

## Root cause

`build_coverage_wrapper` in BOTH test runners flattened only `/` when turning
the spec path into a temp file name:

- `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`
- `src/app/test_runner_new/test_executor_parsing.spl`

```simple
var base = file_path.replace("/", "_")
```

Windows paths arrive with backslashes (`test\01_unit\...`), so `base` kept
`\` separators and `tmp_path` became
`<temp>/simple_cov_test\01_unit\...` — a mixed-separator path whose
subdirectories nobody creates. The wrapper write/read then fails with
ERROR_PATH_NOT_FOUND (os error 3) and the runner fell back.

## Fix

Flatten both separators (the name is then a single flat file directly in the
temp dir, so no parent-dir creation is needed):

```simple
var base = file_path.replace("/", "_").replace("\\", "_")
```

Applied in both runners (2026-09-17). Cosmetic note: the temp name doubles the
`_spec` suffix (`<name>_spec_spec.spl`) because `base` strips `.spl` and
`coverage_wrapper_suffix` re-adds `_spec.spl`; harmless, left as-is.
