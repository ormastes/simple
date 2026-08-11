# Interpreter: 10 drifted duplicate function definitions co-exist in one package

**Status:** OPEN
**Filed:** 2026-08-11
**Layer:** `10.frontend` — core interpreter

## Summary

`src/compiler/10.frontend/core/interpreter/` contains two stale modules,
`eval_access.spl` and `eval_calls.spl`, that duplicate function definitions
already present in the live `_EvalOps/` subpackage
(`access_literal_assign_eval.spl`, `call_method_eval.spl`).

Neither stale module has a single `use`/`import` anywhere in `src/`, `test/`, or
`examples/` — but they are **not dead**. The package uses sibling preloading, so
their definitions are still resolved by name: `eval.spl:445` calls `eval_try`,
which only `eval_access.spl` defines, and `eval_stmts.spl` plus both `_EvalOps`
modules call `val_copy_if_value_struct`, which only `eval_calls.spl` defines.

That means for every duplicated name, **two definitions are co-compiled in the
same package and which one wins is decided by name resolution order**, exactly the
hazard the compiler's own `compiler_cross_module_private_symbol_collision`
warning describes.

## What was already fixed (2026-08-11)

The 12 duplicates whose bodies were **byte-identical** were deleted from the two
stale modules. Removing them cannot change behaviour whichever copy won, and the
codegen diagnostics were verified identical before and after (A/B run of
`use compiler.core.interpreter.eval_ops.*`, same three pre-existing
`unresolved identifier` lines, no new parse errors).

Removed from `eval_access.spl`: `eval_array_lit`, `eval_tuple_lit`,
`eval_struct_lit`, `eval_compound_assign_expr`, `eval_return_expr`,
`eval_enum_variant_call`, `eval_enum_variant_access`, `eval_list_comp`,
`eval_dict_comp`.
Removed from `eval_calls.spl`: `parse_float_text`, `char_digit`,
`eval_struct_constructor`.

## What remains — the 10 DRIFTED pairs

These have the same name in both modules but **different bodies**, so deleting
either copy is a semantic change, not a dedupe. They were deliberately left
alone rather than merged blind.

| function | stale copy | live `_EvalOps` copy |
|---|---|---|
| `eval_field_access` | `eval_access.spl:17` | `_EvalOps/access_literal_assign_eval.spl:363` |
| `eval_index_expr` | `eval_access.spl:87` | `_EvalOps/access_literal_assign_eval.spl:405` |
| `eval_slice_expr` | `eval_access.spl:132` | `_EvalOps/access_literal_assign_eval.spl:450` |
| `eval_dict_lit` | `eval_access.spl:260` | `_EvalOps/access_literal_assign_eval.spl:582` |
| `eval_assign_expr` | `eval_access.spl:285` | `_EvalOps/access_literal_assign_eval.spl:601` |
| `eval_interpolated_string` | `eval_access.spl:501` | `_EvalOps/access_literal_assign_eval.spl:827` |
| `eval_null_coalesce` | `eval_access.spl:513` | `_EvalOps/access_literal_assign_eval.spl:846` |
| `eval_lambda` | `eval_access.spl:613` | `_EvalOps/access_literal_assign_eval.spl:897` |
| `eval_call` | `eval_calls.spl:100` | `_EvalOps/call_method_eval.spl:120` |
| `eval_function_call` | `eval_calls.spl:218` | `_EvalOps/call_method_eval.spl:242` |

(Line numbers for the stale copies are as of the pre-cleanup revision; the
duplicate-removal commit shifts them upward.)

## Why this was skipped rather than merged

Resolving each pair requires knowing **which copy actually executes** and then
diffing the two bodies for behaviour the winner would lose. Establishing that on
the live lane needs a pure-Simple compiler — the deployed `bin/simple` is
currently the Rust seed and announces itself as such, and a full bootstrap was
out of scope for this pass. Merging on the basis of "the `_EvalOps` copy looks
newer" would be exactly the blind merge the dedupe rules forbid.

## Suggested fix

1. On a pure-Simple lane, plant a level-gated tracer in both copies of one pair
   (e.g. `eval_lambda`) and run any spec that evaluates a lambda, to establish
   the resolution winner empirically.
2. For each pair, diff the two bodies and fold any behaviour unique to the loser
   into the `_EvalOps` copy.
3. Move the four genuinely-unique functions — `eval_try` (from `eval_access.spl`)
   and `interp_struct_is_value_type` / `val_struct_deep_copy` /
   `val_copy_if_value_struct` (from `eval_calls.spl`) — into the `_EvalOps`
   package, then delete `eval_access.spl` and `eval_calls.spl` outright.

## Related

- `test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl`
- `test/01_unit/compiler/interpreter/dict_literal_dispatch_spec.spl`
- `test/01_unit/compiler/interpreter/text_byte_at_dispatch_spec.spl`
- `test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl`

All four pin `_EvalOps/*` as the live dispatch path and stayed green (7/1/5/7
passed, 0 failed) across the identical-duplicate removal.
