# Bug: spipe_matchers FatArrow parse regression blocks EAX + OCB3 spec runs

**Date:** 2026-05-02  
**Severity:** Medium (blocks KAT verification in interpreter mode)  
**Affects:** `test/unit/os/crypto/eax_kat_spec.spl`, `test/unit/os/crypto/ocb3_kat_spec.spl`

## Symptom

```
bin/simple test test/unit/os/crypto/ocb3_kat_spec.spl
  FAILED (101ms)
  Error: parse error: Unexpected token: expected expression, found FatArrow

bin/simple test test/unit/os/crypto/eax_kat_spec.spl
  FAILED (100ms)
  Error: parse error: Unexpected token: expected expression, found FatArrow
```

## Pre-existing regression

OCB3 is a pre-existing, known-good spec that was not modified. It fails with the
identical error, confirming this is an environment regression unrelated to the EAX
implementation added in this session.

## Root cause (hypothesis)

The test runner loads both the spec file (`*_spec.spl`) and a companion shadow file
(`.spipe_matchers_*_spec.spl`) together. The shadow files are auto-generated and
contain an older `expect X == Y` syntax form that triggers a FatArrow parse error
when the parser encounters the `=>` in a match arm appearing later in the same
loaded unit.

The spec files themselves use correct `expect(X).to_equal(Y)` syntax and parse
cleanly in isolation (verified: `bin/simple test /tmp/eax_full.spl` passes).

## Workaround attempts

1. Rewrote all `expect X == Y` → `expect(X).to_equal(Y)` in both `.spipe_matchers_*`
   files using `sed -i` — verified 7 `to_equal` replacements per file on disk.
2. Test still fails after fix, suggesting either:
   a. The runner regenerates the matchers file on each run from an internal template, or
   b. There is a second parse error source not yet identified.

## Repro steps

```bash
# Shows pre-existing failure (OCB3 not touched):
bin/simple test test/unit/os/crypto/ocb3_kat_spec.spl

# Shows same failure for new EAX spec:
bin/simple test test/unit/os/crypto/eax_kat_spec.spl

# Spec passes from /tmp (no shadow file present):
cp test/unit/os/crypto/eax_kat_spec.spl /tmp/eax_full.spl
bin/simple test /tmp/eax_full.spl  # → PASSED
```

## Impact

- `src/os/crypto/eax.spl` lints clean and is correct per code review
- `test/unit/os/crypto/eax_kat_spec.spl` has correct syntax per code review
- KAT vectors cannot be verified in interpreter mode until this is resolved
