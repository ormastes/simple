# `fold_gen.spl`'s `_semantic_value_lines` still passes a `Some` box into non-optional encoders

- **Date:** 2026-10-24
- **Status:** OPEN — same defect class as `0e2d7ab2997`, in a sibling emitter in
  the SAME generator file, not covered by that fix
- **Files:** `src/app/compiler_schema/fold_gen.spl` (`_semantic_value_lines`, :312-329),
  `src/compiler/10.frontend/generated/ast_semantic_value.spl` (its output)
- **Related:** `0e2d7ab2997` "fix(schema): fold walkers unwrap optional node
  payloads (Stage 2 [] SIGSEGV)" fixed `_fold_lines` in this same file

## What `0e2d7ab2997` fixed, and what it did not

That commit fixed `_fold_lines` (`fold_gen.spl:488-500`): an optional node
payload holds a `Some` box, so passing it straight to a walk function made
native Stage 2 read the box header as a node and SIGSEGV on every `[]` literal.
It now emits `match` / `case Some(optN)` / `case nil`, and regenerated
`hir_visitor.spl` and `ast_visitor.spl`.

`_semantic_value_lines`, 170 lines earlier in the same file, has the identical
defect and shares no code with `_fold_lines`, so it was not touched.

## The defect

`fold_gen.spl:316-329`, optional branch:

```simple
if optional:
    var out = indent + "if " + v + " == nil:\n"
    out = out + indent + "    state = _ast_semantic_mix_tag(state, \"nil\")\n"
    out = out + indent + "else:\n"
    out = out + indent + "    state = _ast_semantic_mix_tag(state, \"some\")\n"
    val present_type = _strip_opt(type_text)
    if present_type.starts_with("[") and present_type.ends_with("]"):
        # @workaround bug=optional_array_payload_narrowing_native_2026_10_21 ...
        val present_value = "semantic_present{idx}"
        out = out + indent + "    val " + present_value + ": " + present_type + " = " + v + "!\n"
        return out + _semantic_value_lines(u, present_type, present_value, indent + "    ", idx)
    return out + _semantic_value_lines(u, present_type, v, indent + "    ", idx)
```

The `[...]` case force-unwraps with `!`. **Every other present type falls
through to the last line and recurses on `v`, which is still `T?`** — the box.
The recursion then emits, for a node, `state = <encoder>(v, state)`, and for a
prim, `_semantic_primitive_expr(..., v)` — both into parameters declared
non-optional (e.g. `ast_semantic_encode_expr(node: Expr, …)` at
`ast_semantic_value.spl:68`, `…_stmt(node: Stmt, …)` at `:429`).

**The array special-case is itself the admission that the guard does not
narrow.** Its own `@workaround` reads
`reason=old_producer_does_not_narrow_optional_array_after_nil_guard`. If the
`== nil` guard narrowed the binder, that unwrap would be unnecessary. It does
not, so the other types are equally unnarrowed — they just lack the unwrap.

## Live sites in the generated output

`src/compiler/10.frontend/generated/ast_semantic_value.spl`:

| line(s) | call | payload declaration |
|---|---|---|
| 231-235, 1505 | `ast_semantic_encode_block(b_If_f2, state)` | `If(Expr, Block, Block?)` `parser_types_expr.spl:551` |
| 1516, 1539 | `encode_block(b_IfChain_f1 / b_TryCatch_f2)` | `:552`, `:555` |
| 1469, 1474, 1480 | `encode_expr(b_Range_f0 / f1 / f3)` | `Range(Expr?, Expr?, bool, Expr?)` `:544` |
| 1581, 1589 | `encode_expr(b_Yield_f0 / b_Return_f0)` | `:568`, `:569` |
| 1627, 2074 | `encode_enum_payload(b_EnumLit_f2)`, `encode_enum_pattern_payload(b_Enum_f2)` | `:576`, `:732` |
| 2277, 2287, 2292, 2302, 2312 | `encode_type(b_Val_f1 / b_Var_f1)`, `encode_expr(b_Var_f2 / b_SharedVal_f2 / b_SharedVar_f2)` | `:776-779` |
| 1460 | `encode_assign_op(b_Assign_f1)` | `Assign(Expr, AssignOp?, Expr)` `:543` |
| 2452 | `encode_expr(b_Array_f1)` | `Array(Type, Expr?)` `:63` |
| 784 | `encode_expr(node.output_value)` | struct field |

## Reachability

Not dead code. `ast_semantic_value.spl` is called from
`module_surface_semantic_projection.spl:114-122` (`_surface_expr_digest`,
`_surface_type_digest`, `_surface_block_digest`), consumed by
`module_surface_declarations.spl` and `module_surface_source_identity.spl` —
HIR lowering's module-surface digest, on the ordinary compile path.

## Severity, stated honestly

Two distinct consequences, and they differ:

- **Node payloads** reach a non-optional node parameter. This is bit-for-bit the
  shape that SIGSEGVed in `_fold_lines`. Latent crash.
- **Prim payloads** reach `_semantic_primitive_expr`, which does e.g.
  `<v> as i64`. That mixes the BOX's bits into a digest instead of the value —
  a wrong digest, silently, not a crash.

**Not established:** whether native codegen narrows a `T?` local after a
`== nil` guard in some cases. The only in-repo evidence is the array
`@workaround` above, which asserts it does not — for arrays. No crash has been
observed at these specific sites; `0e2d7ab2997`'s crash was in `_fold_lines`,
where there was no guard at all. So this is filed as the same class by
construction, not as a reproduced failure.

## The fix

Hoist the existing array unwrap to every present type — delete the
`present_type.starts_with("[")` condition and always bind
`val semantic_present{idx}: {present_type} = {v}!` before recursing. The
`"nil"`/`"some"` tags and the recursion shape are unchanged, so only the value
handed to the encoder changes, from the box to the payload.

**Digest consequence, which must be stated before anyone lands this:** for
optional NODE and PRIM payloads the mixed bytes change, because today the box is
mixed and after the fix the payload is. Module-surface digests therefore move.
That is a correction, not a regression — the current value is the box's
address/header bits — but it will invalidate anything keyed on those digests.

## Why this record instead of the fix

The fix needs `ast_semantic_value.spl` regenerated in the same change, or the
generated output goes stale against its generator — the exact drift class this
repo has been bitten by repeatedly. **Regeneration is not possible on this host
right now:** the deployed seed cannot parse a current stdlib file —

```
$ bin/simple run src/app/compiler_schema/main.spl folds <out>
error: compile failed: parse: in src/lib/nogc_sync_mut/io/windows_redirected_process.spl:
       Unexpected token: expected Fn, found Colon
```

— and `bootstrap/stage*/simple` is the bootstrap CLI, which has no `run`. So the
generator edit is deliberately NOT landed here. Whoever regenerated
`hir_visitor.spl` for `0e2d7ab2997` has a working path and should apply it,
regenerating in the same commit.

## Spec-pin gap

`test/01_unit/compiler/hir/hir_generated_optional_child_spec.spl:85-87` pins only
`hir_visitor.spl` text. Nothing pins `ast_semantic_value.spl`, so a regression
here is caught by no test. The pin should cover every file the changed generator
writes, which for `fold_gen.spl` is `hir_visitor.spl`, `ast_visitor.spl`,
`ast_semantic_value.spl` (`fold_gen.spl:698`, `:765`) and
`10.frontend/generated/__init__.spl` (`:660-672`).
