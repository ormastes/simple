# Forced-JIT lint of a warning-free target crashes: unwrap on None (rc 127)
## Registered 2026-11-27 by p3sweep3 lane (exposed by closing seed_jit_coverage_self_hosted_compiler_2026-08-21)

**Status:** OPEN
**Severity:** P3
**Lane observed:** Windows x86_64, fresh tree-built seed

## Symptom

With the lint entry closure truly on the JIT lane (after the
seed_jit_coverage_self_hosted_compiler_2026-08-21 import repoint), linting a
WARNING-FREE target on the forced-JIT lane crashes fail-closed:

```
error: called unwrap on None
rc 127
```

Any clean `.spl` file reproduces in ~18s with the JIT lane forced. Masked
previously because every forced-JIT lint de-JITted to the interpreter first.
The default lint lane is interpreter-by-design (`reason=lint-jit-parity-unproven`),
so no default-lane user is affected.

Full repro (courtesy of the p3sweep3 wave-8 lane):
`build/p3cache/jitcov/CLOSE-NOTE.md` — force the JIT lane for
`bin/simple lint <clean-file.spl>` and observe the unwrap failure.

## Suspected mechanism

Lint clean-path Option handling under JIT — e.g. `linter.last_resolved_config.unwrap()`
in `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`. The Option is
presumably Some on the interpreter path but None under JIT (field elided or
differently initialized by the JIT closure shape). Verify before fixing; the
suspect is a starting point only.

## Acceptance

A warning-free target lints clean on the forced-JIT lane with the same verdict
as the interpreter lane (0 errors, byte-identical diagnostics), pinned by a
regression spec (SIMPLE_BINARY-overridable per repo convention).
