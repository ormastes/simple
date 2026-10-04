# JIT: a method call on a nullable trait receiver is typed by an unrelated struct's method

- **Filed:** 2026-10-05
- **Area:** `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`
  (`lookup_method_return_type_inner`)
- **Status:** FIXED 2026-10-05

## Symptom

`examples/06_io/ui/rendering/rendering_gui_full.spl` at 3840x2160 ran entirely in
the interpreter (707 s, 4.27 GB RSS):

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'WidgetNode'
field 'ok' (declared fields: id) [in examples/06_io/ui/rendering/rendering_gui_full.spl]:
whole module dropped to the interpreter
```

## Root cause

`src/lib/common/ui/window_scene.spl:267`:

```
if val provider = _wm_background_image_provider:   # BackgroundImageProvider?
    val outcome = provider.resolve(...)
    if outcome.ok:
```

A trait value is ANY in HIR, and `if val` binds `provider` as `Pointer { inner:
ANY }` (`T?`). The trait-signature lookup only ran for a bare ANY receiver, so
this call fell through to the `.resolve` suffix search. No type in the
gui_full unit implements `BackgroundImageProvider`, so the only match was
`ProfileSet.resolve -> WidgetNode` (`src/lib/common/ui/profile.spl:186`), and
the result was typed `WidgetNode`. When an implementor exists, the implementor
and the unrelated struct disagree, so the trait signature was used and the bug
stayed hidden.

Minimal repro: a trait with no implementor, an unrelated struct with a
same-named method, and `if val p = opt_trait: p.method().field`.

## Fix

Treat `Pointer { inner: ANY }` like ANY for the agreed-trait-signature lookup.
The result type is changed only when every trait declaring the method agrees
on it, which is the same rule the bare-ANY receiver already uses.

## Evidence

- Specs in `src/compiler_rust/compiler/tests/trait_receiver_jit.rs`:
  - `nullable_trait_receiver_without_implementor_uses_trait_signature` reproduces the bug. It failed HIR lowering on the pre-fix seed with `struct 'Node' field 'ok'`.
  - `nullable_trait_receiver_with_implementor_reads_trait_result_fields` is the generalization: an implementor is present and the unrelated method keeps its own type.
- rendering_gui_full at 3840x2160, same tree:

  | | wall | RSS | mode |
  |---|---|---|---|
  | before | 707 s | 4.27 GB | interpreted |
  | after | 4.0 s | 0.98 GB | JIT, 0 `jit-fallback` lines |

  The two captures are byte-identical (`cmp`).
