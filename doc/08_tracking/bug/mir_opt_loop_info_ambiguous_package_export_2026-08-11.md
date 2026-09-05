# MIR optimizer `LoopInfo` ambiguous package export

## Status

Fixed in the live pure-Simple source; exact-current Stage 2 requires a new
stable source freeze before retry.

Recovered on 2026-08-11 after a concurrent working-tree overwrite removed the
proven rename while leaving its regression and incident record behind. The fix
was re-derived against the new clean HEAD and the package-resolution regression
was rerun once.

## Reproducer

The admitted 11,862-file Stage-2 source snapshot failed package discovery with:

`ambiguous package export LoopInfo` from `auto_vectorize_types.spl` and
`loop_detect.spl` through `mir_opt/__init__.spl`.

Cycle-1 evidence is retained in
`build/mini_builds/mission_critical_exact_stage2_20260811/`. It exited 1 before
object emission in 10.76 seconds with 29,036 KiB maximum RSS. The private cache
remained empty and no output artifact existed.

## Root cause and fix

The two types are intentionally different models but shared the public name
`LoopInfo`. Omitting one explicit initializer export was insufficient because
package discovery still found both public declarations.

The vectorizer-owned model is now named `VectorLoopInfo` throughout its source,
explicit consumers, and tests. `loop_detect.LoopInfo` is therefore the sole
package provider for the bare `LoopInfo` name, while both distinct types remain
resolvable. No discovery first-provider rule or ambiguity bypass was introduced.

Regression coverage:

- `test/01_unit/compiler/mir_opt/loop_info_package_export_spec.spl`

The regression imports both types through the real package surface, which makes
package resolution itself part of the check, and separately verifies that the
vectorizer declaration no longer provides the bare `LoopInfo` name.
