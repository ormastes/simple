# Simple Runtime Unavailable for Modern GUI Evidence

Date: 2026-06-26

## Summary

The modern GUI Web WM evidence lane cannot run its SPipe checks in this checkout because no working Simple runtime is available.

## Reproduction

```bash
bin/simple --version
bin/release/simple --version
bin/simple_native --version
```

## Observed

- `bin/simple` is missing.
- `bin/release/simple` exits `127` because it points to missing `bin/release/x86_64-unknown-linux-gnu/simple`.
- `bin/simple_native --version` exits `139`.
- `src/compiler_rust/target/release/simple --version` succeeds and is usable as
  the current local fallback.

The modern GUI wrapper records the same blocker in:

```text
build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/evidence.env
```

## Impact

The deployed wrapper paths remain broken, but the modern GUI evidence lane can
run with `src/compiler_rust/target/release/simple`.

The following exact `bin/simple ...` commands remain blocked until the deployed
wrapper is restored:

```bash
bin/simple test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter
bin/simple spipe-docgen test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl --output doc/06_spec --no-index
bin/simple test test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl --mode=interpreter
```

## Expected

At least one deployed runtime should be available at `bin/simple`,
`bin/release/simple`, or another documented wrapper path so SPipe lanes can run
without depending on a segfaulting local native binary.
