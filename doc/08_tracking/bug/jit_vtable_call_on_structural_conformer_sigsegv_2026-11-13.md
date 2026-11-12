# JIT trait vtable call on a structural (no `with`) conformer SIGSEGVs

- **Filed:** 2026-11-13
- **Status:** JIT FIX IN LANE `work/jit-dynamic-dispatch-20261113` (clean runtime error). The AOT/native lane is NOT fixed (see Scope).
- **Related:** `doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md` (finding a),
  `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02` (duck sentinel, a different shape)

## Symptom

```
trait Reducer:
    fn ident() -> text
    fn bits() -> i64
class D:                      # same methods, no `with Reducer`
    n: i64
    fn ident() -> text: "d"
    fn bits() -> i64: self.n
class Slot:
    r: Reducer
fn f(slot: Slot?) -> text:
    if val Some(s) = slot:
        val x: Reducer = s.r
        return x.ident()
    "none"
```

`f(Some(Slot(r: D(n: 9))))` under the Cranelift JIT (seed `a64ac53aaf6ca014`,
`origin/release/1.0.0` `fe75b13a584`) dies with **SIGSEGV, rc 139**. The same
call with `class C with Reducer` prints the right value (`c7`).

## Cause

A trait-typed receiver (a parameter, an annotated local, or, after this lane,
a field-initialised local) lowers to `MirInst::MethodCallVirtual`.
`compile_method_call_virtual` loads `object[0]` as the vtable pointer and then
calls `vtable[slot]`. Only a class that declares the trait gets a vtable word
at offset 0 (`compile_struct_init`, keyed on `vtable_data_ids`). A
duck-conforming class starts with field 0 instead, so the JIT loads `n` (9) as
a vtable pointer and jumps through it. A NIL receiver crashes the same way,
because it masks to address 0.

## Fix (JIT)

1. **Sole structural conformer, trait not implemented**
   (`mir/lower/lowering_expr_method.rs`). This is the symptom above. If the
   trait has no implementation in the unit and exactly one class conforms
   structurally, a declared-trait receiver now binds that class by name
   (#8683's bind). It no longer emits a vtable load that the object cannot
   satisfy. The example now returns `d` / `9`.
   - Test: `sole_structural_conformer_keeps_the_by_name_bind`.
2. **Every other virtual call under the JIT**
   (`codegen/instr/closures_structs.rs` `emit_jit_vtable_receiver_guard`).
   Under `JITModule` the unit is the whole program, so every stamped vtable is
   a local data object. The loaded word is compared against that set.
   - On a miss, including a NIL receiver, the call goes to
     `rt_method_not_found`, which exits 70 with `Runtime error: Method ... not
     found`. It no longer jumps through field data.
   - This covers a structural conformer when the trait *is* implemented
     elsewhere in the unit, and a trait with two or more structural
     conformers.
   - Test: `structural_conformer_fails_cleanly_not_sigsegv` (C implements,
     D reaches the call).

Both tests are in
`src/compiler_rust/compiler/tests/jit_trait_local_vtable_dispatch.rs`.

## Scope / still open

- **AOT / native-project:** not guarded. Vtables can live in other object files
  (`vtable_symbol`, `Linkage::Export`), so the local set is incomplete and a
  guard there would reject valid receivers. A native-build fix needs either a
  per-trait identity in the vtable, or a vtable for structural conformers at
  the coercion site.
- **Semantics:** a structural conformer is still not *dispatchable* under the
  JIT. It is now refused cleanly instead of crashing. Making it work means
  giving the class a vtable when it is coerced to the trait. That is an owner
  decision.
- **Multi-trait objects:** an object carries ONE vtable (first registration
  wins, `emit_vtable_data_objects`). The guard accepts any stamped vtable, so it
  does not change behaviour for an object that carries a vtable for a
  *different* trait. That existing hazard is unchanged.
