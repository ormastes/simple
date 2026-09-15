# Wave coverage wrapper fails specs that pass plain `bin/simple run` (2026-09-15)

- Observed: in the 2026-09-15 test wave, 38 specs under `test/01_unit/lib/nogc_async_mut*/`
  were reported FAIL, but every one of them passes plain `bin/simple run <spec>`
  (outcome=OK, failed=0). Proof example: `test/01_unit/lib/nogc_async_mut/tls/ech_spec.spl`
  — wave log shows `Undefined("undefined identifier: chr")` from the MC/DC-wrapped
  temp file (`/tmp/spipe_wrapped__tmp_simple_cov_..._spec_native.spl`), while the plain
  run is 6/6 green.
- Root cause (class): the wave harness wraps each spec into a coverage-instrumented
  native file and, when that file cannot compile (`cannot compile to standalone SMF:
  NN function(s) contain constructs that require the interpreter`) or hits wrapper-only
  semantic errors (undefined `chr`/`Dict`/`Platform`/`parse`/`NativeTensor`, struct
  field renames visible only in the wrapped compile), the whole spec is failed, even
  though the un-wrapped spec is green.
- Scope: 38 specs (verdict table: plain-run batch in `/tmp/ax_plain_verdicts.txt`,
  wave log `/tmp/simple_testwave/logs/test_01_unit_lib_nogc_async_mut.log`).
- Unblock condition: the wave runner must fall back to plain interpreter execution
  when the wrapped compile fails (the same `[mcdc-fallback]` degradation that already
  exists and yields PASS for sibling specs), instead of recording a FAIL.
- Not spec-side drift: editing these specs cannot change the wave verdict; they are
  intentionally left as-is.
