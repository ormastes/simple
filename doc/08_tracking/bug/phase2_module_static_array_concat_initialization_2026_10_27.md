# Pinned Phase 2 cannot initialize DevHub module static arrays by concatenation

- Canonical ID: `phase2_module_static_array_concat_initialization_2026_10_27`
- Status: open; source compatibility does not close the underlying bug.
- Owner: DevHub / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
- Source: `src/app/devhub/gh_compat.spl`.
- Regression: `test/01_unit/app/devhub/gh_compat_spec.spl`.

The compatibility flag catalogs retain literal typed arrays instead of executing array concatenation while initializing module statics. Their public values remain unchanged. This is narrower than ordinary function-local array concatenation, which remains supported by other focused checks.

## Evidence

The retained literal tables were part of the earlier DevHub P2 source repair. Current GH JSON and flag native graphs compile and run successfully, but this is not a new independent replay of the original static-initializer failure. Related older registry issue native_array_concat_dispatch_bootstrap_2026_10_16 remains separate.

## Removal condition

Retire only after actual module-static concatenation preserves every flag value and method/type metadata under the deployed producer, with native command flag regressions and no startup evaluation error.

Commit identity and final receipts must be appended through the canonical BugDatabase API after integration. No compiler rebuild, standard SSpec execution or unexecuted matrix is claimed.

**Revalidated 2026-11-02: still plausible because open; source compatibility does not close the underlying bug; no merged fix commit with a passing regression is cited in this doc.**

**2026-11-03 (sonB): deferred, pointer.** `infer_unfolded_static_expr_type_bounded` (`50.mir/_MirLowering/module_lowering.spl:234`) has no Array case for `Binary(Add)` of two module-static arrays (only scalar/text), so the Infer branch at ~3689 errors. Fix: add an array-typed Add arm reusing the array-literal inference used by the unannotated-global spec. Needs stage3 to verify.

**2026-11-03 (sonB): fix-implemented-verification-pending.** `infer_unfolded_static_expr_type_bounded` (`module_lowering.spl`) now accepts a settled HIR Array type and keeps the array MIR type for `Add` of array operands. Spec: "module static array concatenation" in `test/01_unit/compiler/mir/unannotated_module_global_static_type_spec.spl`. Verify on stage3, then retire the literal tables in `src/app/devhub/gh_compat.spl` in a separate commit.

**2026-11-03 (fixlane): earlier MIR-only change did not work; real fix landed.** Running the spec added by 311cff40659 on the seed-interpreted compiler FAILED (`undefined field 'kind' on nil`, then storage `missing`): `expr.type_` is optional, and the unannotated `pub val ALL = A + B` const stayed `HirTypeKind.Infer`, so the importer path (`register_provider_global_bindings`) hit "lacks a resolved storage type" and the owner path (`lower_static`) never took the array arm. Fix: HIR `lowered_const_value_type` (`trait_impl_lowering.spl`) now settles `A + B` over two arrays of one settled type (and accepts Array-typed const refs), so owner and importer agree on array storage; `lower_static` Binary arm uses the settled array HIR type; the `module_lowering.spl` guard is nil-safe. Spec "module static array concatenation" now PASSES (13/13 in `unannotated_module_global_static_type_spec.spl`; 40/40 `trait_impl_lowering_mcdc_spec`, 2/2 `infer_empty_array_full_closure_spec` unchanged).
Remaining (verification-pending): the literal flag tables in `src/app/devhub/gh_compat.spl` are intentionally KEPT until a stage3 built with this fix runs the native DevHub flag regression. Retire steps: (1) `bin/simple test test/01_unit/compiler/mir/unannotated_module_global_static_type_spec.spl` on the new stage3 (expect 13/13); (2) replace the six `*_KNOWN` literal arrays with `_COMMON_KNOWN + [...]`, drop the `@workaround` line; (3) `bin/simple test test/01_unit/app/devhub/gh_compat_spec.spl` plus a native build of the devhub graph with no startup evaluation error.
