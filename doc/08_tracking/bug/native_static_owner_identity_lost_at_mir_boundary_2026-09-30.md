# Static owner identity is lost before native MIR dispatch

Status: source fix and regressions prepared; execution against the corrected producer is pending.

The Windows producer `0be6e4c2a802e4fa7993fde80003eb87ffae097e564adb82ab4c937bbc640161` (source4a5a4ca1576177c28b84b4e0f276c8160e99259d) passes HIR and ABI traversal for the two-class method fixture, confirming progress past the previous method-map crash. Native compilation then exits1 at MIR: `undefined variable First`, `undefined variable Second`, and `unresolved method call: answer`. The failed compilation took3.259s. Evidence is retained in `D:/dev/simple-windows-corrected-early-phases-20260930-producer-hir-attempt1/method-regression/compile.result.json` and its stdout log. This is a semantic lowering failure, not inventory or admission refusal.

`expr_dispatch.spl` intentionally supplies empty owner hints to `lower_method_call` because extracting a receiver's nested payload while matching MethodCall previously caused native allocation loops. The conservative leaf-name fallback cannot disambiguate `First.answer` and `Second.answer`. It falls through to treating the class receiver as a runtime value.

Resolve a declared static method while HIR still owns the receiver. The helper accepts only Class, Struct or Enum symbols and looks up the method through that exact owner. It records the existing `MethodResolution.StaticMethod(owner, method)` variant. Both expression lowering paths retain the result. MIR uses its existing resolved static-call branch, avoiding the problematic nested receiver match. Variables, parameters, instance methods, missing owners and missing methods retain unresolved dispatch for the normal semantic stages.

Policy coverage: `declared_static_method_resolution_spec.spl` checks two classes with the same method name, ordinary instance dispatch, nonstatic rejection, imported and enum identities, and absent owners/methods. Native coverage retains the original two-class fixture (expected42) and adds `native_static_owner_identity/main.spl` plus its provider (two local static owners, an instance, an imported class and an enum; expected65).

Neither these policy tests nor the added native fixture have passed on a newly rebuilt producer yet. Preserve this distinction from the source review and from the live full Phase3 attempt, which remains independent.
