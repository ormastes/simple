# Redeploy Kit 03 — inherited trait default method SEGFAULT

## Defect (crash, critical)
Calling a trait DEFAULT method that a struct inherits without overriding it
segfaults (exit 139).

```
trait Greetable:
    fn greet_formal() -> text: "Good day"
    fn greet_casual() -> text: "Hey"
struct Person: name: text
impl Greetable for Person:
    fn greet_casual() -> text: "Yo"   # overrides ONLY greet_casual
fn main():
    val p = Person(name: "Alice")
    print(p.greet_casual())   # "Yo" — OK
    print(p.greet_formal())   # SEGFAULT — inherited default
```

## Root cause (analysis — not yet fixed)
`p.greet_casual()` (overridden) resolves and runs; `p.greet_formal()`
(inherited, non-overridden default) crashes. This points at **virtual/method
dispatch failing to fall back to the trait default body** when the
`impl Greetable for Person` block does not define the method.

Relevant codegen: `compile_method_call_virtual` /
`compile_method_call_static` in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`. The likely
failure is a NULL (or uninitialised) function pointer in the vtable slot for
`greet_formal` on `Person`: the vtable/method table is populated from the
`impl` block's methods only, and the inherited default is never copied into the
slot, so the slot holds NULL (or a stale address). The subsequent indirect call
jumps to it → SIGSEGV. This mirrors the `compile_closure_create` "storing NULL"
fallback path where an unresolved function pointer is stored as 0.

Fix direction (requires seed rebuild to verify): when building a struct's method
/ vtable table for an implemented trait, seed every trait method slot with the
trait's DEFAULT body first, then overlay the `impl` block's overrides. No slot
should ever remain NULL for a method the trait declares with a default. Add a
codegen assertion/guard that a virtual dispatch never calls a NULL pointer
(trap with a diagnostic instead of jumping to 0).

## Test plan
- Expected-behavior spec:
  `test/cert/redeploy_pending/trait_default_method_inherited.spl`
  (expects `Yo` then `Good day`, exit 0 — no crash).

## Verify-now vs redeploy-pending
- REDEPLOY-PENDING + NOT-YET-FIXED: root cause localized to trait-default vtable
  population in the frozen seed codegen; fix not implemented/verified this
  session. A crash-class defect must not be claimed fixed without a rebuilt
  binary that no longer segfaults.
