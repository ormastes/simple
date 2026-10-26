# Header generator named facade has no source module

Status: local candidate; executable verification and performance admission pending.

Committed source `abb0891dcc048958ea2030759802ad7ae0cedc76` declares `mod mod_`
and exports three names from it in `compiler/90.tools/header_gen/__init__.spl`.
`driver_api_project_build.spl` also imports `HeaderGenerator` from this named
module. No `header_gen/mod_.spl` exists in that tree; the declarations live in
`header_gen/mod.spl`. Test-runner capture found three unresolved facade exports.
The conservative host closure scan is evidence of the missing file, not a native
compiler failure or an authoritative full closure validation.

The local repair adds a thin `mod_.spl` export facade to the existing declarations.
It preserves direct `mod` callers and has no duplicated class or function bodies.
The native entry resolver has no observed implicit `mod_` to `mod` rewrite.

Regression: `test/01_unit/compiler/tools/header_gen_facade_spec.spl` exercises
result construction, valid headers, missing exports, and parity with the direct
validator. Authored before adding the facade; executable baseline/candidate
results are **UNRUN**, so no TDD execution PASS is claimed.

Remaining: compile and execute the regression on a qualified pure compiler;
verify both import paths retain one implementation owner; measure preparation
and build time/RSS with the same inputs and limits. Adding an export module is
not itself a performance improvement. Keep this candidate local until the user
required Phase3 and non-regression gates pass. Canonical bug DB reconciliation
is pending availability of the qualified DB tool.
