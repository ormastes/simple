# Native path: lambda-capture scan explicitly excludes interpolated string literals, so outer variables used only inside `"{...}"` in a lambda body are "undefined"

**Date:** 2026-07-17
**Severity:** Medium-High (loud build failure, but a real functionality gap:
any closure that references a captured variable only through string
interpolation cannot build at all)
**Status:** open
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom

```simple
fn main():
    val inner = 9
    val f = \y: "{inner}"
    print "LB3:{f(5)}|END"
```

- Oracle: `LB3:9|END`
- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): fails to build:
  ```
  error: MIR lowering error: undefined variable: inner
  ```

Bisected against a control that captures the same outer variable in the same
lambda but WITHOUT going through string interpolation:

```simple
fn main():
    val inner = 9
    val f = \y: y + inner
    print "LB2:{f(5)}|END"
```

This one builds and runs correctly on both oracle and native
(`LB2:14|END`). So lambda closures over outer variables work in general —
only the interpolation case is broken.

## Root cause (found via code read, exact line)

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, function
`lambda_capture_scan_supported` (~line 1949), decides whether a lambda body
can be scanned for the free variables it needs to capture
(`"""True when collect_free_var_syms traverses the whole expression."""`).
Line 1953:

```
case StringLit(_, interps): not interps.?
```

A string literal is only considered "capture-scan supported" when it has
**no** interpolations (`interps` is absent). If the string literal has any
`{...}` interpolation, this returns `false` for the whole literal — and,
because `lambda_capture_scan_supported` composes recursively (e.g. `Binary`
requires both sides supported, `Block` requires every statement supported),
a single interpolated string literal anywhere in a lambda body makes the
**entire lambda body** unsupported for capture scanning. The caller
(~line 2029: `if captures and not self.lambda_capture_scan_supported(body):`)
then evidently skips wiring up the capture for at least the variables
referenced only inside the interpolation, so the MIR lowering of the
lambda body later hits a genuinely free/uncaptured reference to `inner` and
fails with "undefined variable."

## Expected

`lambda_capture_scan_supported` (and whatever `collect_free_var_syms`
traversal it gates) must recurse into a `StringLit`'s `interps` field the same
way it already recurses into `Binary`/`Call`/`Block`/etc., discovering free
variables referenced inside `{...}` placeholders exactly as it would if the
same expression appeared outside a string literal.

## Suggested direction

- Add an `interps`-aware branch to `lambda_capture_scan_supported`'s
  `StringLit` case: instead of `not interps.?`, iterate the interpolation
  parts (whatever `HirExpr`/segment type `interps` holds) and require
  `lambda_capture_scan_supported` to hold for each embedded expression too —
  mirroring the existing recursive composition pattern used for `Binary`,
  `Call`, `MethodCall`, `Block`, etc. in the same function.
- Cross-check whatever `collect_free_var_syms` (referenced in this function's
  docstring) does for non-lambda contexts — it likely already has to walk
  `interps` correctly for ordinary (non-lambda) interpolated strings to work
  at all, so the actual free-variable-collection logic for interpolation may
  already exist and just needs to be reused/exposed to this capture-scan
  gate, rather than reimplemented.
- This is core lambda/closure codegen shared by every lambda in the native
  path — verify against the full smoke matrix
  (`sh scripts/check/native-smoke-matrix.shs`, fail=0,
  codegen_fallback_hits=0) after any fix here, not just this lane's probes.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).
- Bisected with a direct-reference control (no interpolation) in the same
  lambda shape, which builds and runs correctly on both paths, isolating the
  defect to the interpolation-specific capture-scan exclusion.
