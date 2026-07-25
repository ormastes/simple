# FontRenderConfig `identity()` / `valid()` methods miscompile under entry-closure receiver-binding

**Date:** 2026-07-18
**Status:** Worked around (methods converted to typed free functions); the
underlying entry-closure **receiver-binding codegen miscompile is OPEN** at the
seed/codegen level.
**Severity:** P1 — first-frame fault storm (81 recovered faults per frame down
to 1 after the workaround) on the SimpleOS x86_64 desktop.
**Component:** compiler codegen — `--entry-closure` method receiver (`self`)
binding on the freestanding cranelift path.

## Symptom

Calling the `FontRenderConfig.identity()` and `FontRenderConfig.valid()`
instance methods inside the x86_64 `--entry-closure` baremetal kernel
miscompiles the method receiver binding, producing a first-frame fault storm
(81 recovered faults on the first composed frame). Hosted builds are unaffected.

## Root cause

Entry-closure method dispatch binds the `self`/receiver incorrectly for these
config methods, so the method body reads a wrong/nil receiver. This is a
receiver-binding miscompile, **distinct from** the Option-unwrap class and from
the imported-class instantiation fault (see cross-references) — the value being
mis-bound is the method's own receiver, not an unwrapped Option and not a
freshly-instantiated imported class.

## Fix (workaround)

`94a893e77b9` fix(font): FontRenderConfig `identity()`/`valid()` -> typed free
functions — takes the config as an explicit typed parameter instead of relying
on receiver binding, sidestepping the miscompile. First-frame fault storm
dropped 81 -> 1.

## Affected files

- `src/lib/nogc_sync_mut/text_layout/font_types.spl`
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`
- `src/lib/common/text_layout/font_render_config_spec.spl` (characterization)

## Required root fix

Fix the entry-closure receiver-binding lowering so instance methods on
value-typed config structs bind `self` correctly on the freestanding cranelift
path, then the free-function conversion above can be reverted. Add a regression
test that calls an instance method on a value struct under `--entry-closure
--backend cranelift --target x86_64-unknown-none` and asserts the receiver's
fields read correctly.

## Related / cross-references

- `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md` — the
  freestanding entry-closure codegen defect log (C1–C8). `b53adfc281e` recorded
  "4 entry-closure codegen defects" there (module-global init, `if val` nil,
  short-circuit `and` dropping its left operand, anonymous-tuple member swap);
  this receiver-binding miscompile is a related freestanding entry-closure
  codegen defect in the same family.
- `baremetal_entry_closure_class_instantiation_fault_2026-07-06.md` — related
  entry-closure fault, but on imported-class **instantiation**, not method
  receiver binding.
- `baremetal_option_field_unwrap_faults_class_2026-07-18.md` — sibling
  freestanding codegen class (Option unwrap / `if val`).
