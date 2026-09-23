# Native optional tuple pattern can accept nil as Some

Status: OPEN compiler lowering defect; package comparator uses an explicit
nested-match compatibility form. Do not claim the general pattern is repaired.

Observed with admitted Windows LLVM Stage2 producer SHA256
`0d4134f1328b5197036fa76be067b5f88c9eee9b13015ad44a6cd40dd1d5ce74`.
The legacy semantic-version comparator matched `(a.prerelease, b.prerelease)`
with `(nil, Some(_)) => true` before `(nil, nil) => false`. Equal normal
versions incorrectly satisfied strict Greater. The labeled native regression
failed assertion 23, while the other 33 assertions passed; Range formatting
was not the failure.

Evidence: `build/p2r/semver/resumed-labeled-20260923.log`. Both versions were
1.0.0 with nil prerelease/build; expected `satisfies(v, Greater(v)) == false`,
actual true. Compile and link completed without stubs.

Source corroboration: Rust HIR `expr/control.rs` handles top-level built-in
Some through `rt_is_some`, but `subpattern_condition` does not apply that
built-in optional rule. It may treat Some as a non-enum constructor and return
no condition; `sequence_condition` skips missing conditions. This can omit a
refutable nested test. The exact general compiler correction needs targeted
tuple/array/enum optional-pattern fixtures, including nil, Some, user-defined
Some variants, payload binding and exhaustive negative cases.

The scoped package repair uses nested top-level optional matches, mirroring
the existing modern comparator, and retains strict equality/prerelease order.
Its focused native regression includes all four nil/present combinations and
both unequal prerelease directions. This workaround is recorded rather than
silently declaring the compact tuple syntax unsupported or changing semantics.
