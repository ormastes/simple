# Interpreter: 10 drifted duplicate function definitions — the STALE copies WIN

**Status:** OPEN — DIVERGENCE CONFIRMED, DO NOT DEDUPE
**Filed:** 2026-08-11
**Updated:** 2026-08-11 (resolution winner measured; original premise falsified)
**Layer:** `10.frontend` — core interpreter

## Summary

`src/compiler/10.frontend/core/interpreter/` contains two modules,
`eval_access.spl` and `eval_calls.spl`, that duplicate function definitions
also present in the `_EvalOps/` subpackage
(`access_literal_assign_eval.spl`, `call_method_eval.spl`).

Neither module has a single `use`/`import` anywhere in `src/`, `test/`, or
`examples/` — but they are **not dead**. The package uses sibling preloading, so
their definitions are still resolved by name.

For every duplicated name, **two definitions are co-compiled in the same package
and which one wins is decided by name resolution order.**

## MEASURED: the stale copies win — the `_EvalOps` copies are unreachable

The original filing assumed the `_EvalOps` copies were the live path, on the
strength of four specs said to "pin `_EvalOps` as the live dispatch path".
**Both halves of that assumption are wrong.**

### 1. The four "pinning" specs are source-text greps, not behavioural tests

`dict_literal_dispatch_spec.spl`, `evalops_export_and_text_at_spec.spl`,
`text_byte_at_dispatch_spec.spl`, `option_result_method_dispatch_spec.spl` all
work by `rt_file_read_text(<path>)` followed by `expect(...).to_contain("<source
substring>")`. They assert that certain TEXT exists in certain FILES. They never
execute the evaluator. They stay green no matter which copy actually runs, and
they prove nothing about dispatch. Example, verbatim from
`dict_literal_dispatch_spec.spl`:

    expect(owner).to_contain("val_struct_upsert_field(base_val, val_to_text(key_val), new_val)")

That line asserts a string is present in `_EvalOps/access_literal_assign_eval.spl`.
The code containing it **never runs** (see below).

### 2. Structural sabotage probe: the sibling copy wins

Resolution order was measured directly by building a faithful structural model
of the package — same filenames, same `_EvalOps/` subdirectory, same
`eval_ops.spl` containing `export use ..._EvalOps.*`, same `__init__.spl`
re-export block — with each copy of each function returning a distinguishable
constant (`x + 1000` for the `eval_access.spl`/`eval_calls.spl` position,
`x + 2000` for the `_EvalOps` position), run under `bin/simple run`:

| probe | result | meaning |
|---|---|---|
| baseline, all four names | `nc=1001 lam=1001 call=1001 fcall=1001` | **stale copy wins** |
| inverse control, stale side changed to `+7000` | `nc=7001 lam=7001 call=7001 fcall=7001` | tracks the stale file, not a constant artefact |
| stale files deleted | `nc=2001 lam=2001 call=2001 fcall=2001` | fall-through proves the `_EvalOps` copy is what a delete would activate |
| caller uses explicit `use interpreter.eval_ops.*` | `nc=1001 call=1001` | even the explicit `_EvalOps` re-export path resolves to the stale copy |

A reduced repro also showed the winner is **filename-order sensitive** (renaming
the sibling from `a_stale.spl` to `z_stale.spl` flipped the winner), i.e. this is
an accident of ordering, not a designed precedence.

### 3. Independent corroboration already in the tree

`_EvalOps/call_method_eval.spl`, in its own `eval_function_call`, carries this
comment from an earlier, independent probe:

> This `eval_function_call` is a near-identical DUPLICATE of the one in
> `eval_calls.spl`; sabotage-probing both (2026-08-09) showed **eval_calls.spl's
> copy is the live one and this one never executes.**

Two independent methods, two weeks apart, agree.

Note the contradiction this exposes: `eval_access.spl`'s `eval_assign_expr`
comment asserts the opposite ("`_EvalOps/access_literal_assign_eval.spl` ... is
the one `eval_ops.spl` re-exports"). The tree's own comments disagree with each
other; the measurement settles it.

## Consequence: deleting the stale copies is a 10-function behaviour switch

Deleting `eval_access.spl` / `eval_calls.spl` — the "suggested fix" in the
original filing — would silently swap ten evaluator functions for a different
implementation generation. **That must not be done as a dedupe.**

## Per-pair divergence (WINNER = stale; LOSER = `_EvalOps`, currently dead)

| function | winner-only behaviour (would be LOST by a delete) | loser-only behaviour (currently DEAD) |
|---|---|---|
| `eval_field_access` | enum-variant **name validation** before treating `T.x` as a variant; `try_force_any_deferred_for` **lazy-module retry** | — |
| `eval_index_expr` | indexing **any** struct by field name | type-error diagnostics for non-int index; `__dict`-restricted struct indexing |
| `eval_slice_expr` | tolerant defaulting of non-int bounds | type-error diagnostics for non-int slice bounds |
| `eval_dict_lit` | — | key/value evaluated before either is pushed (winner pushes the key first, leaving `field_names` longer than `field_values` on an error path) |
| `eval_assign_expr` | field-index assign on **any** struct; array index-assign bounds error | `val_struct_upsert_field` dict upsert; `__dict`-restricted semantics |
| `eval_interpolated_string` | — | **correct segment interleaving.** The winner joins only the interpolated parts via `parts.join("")`, dropping the literal text segments; the loser reconstructs `seg0 + val0 + seg1 + ...` |
| `eval_null_coalesce` | **Option/enum handling**: `None`/`nil` tag → right side; `Some`/`Ok` → unwrap `__payload` | — (loser handles plain `nil` only) |
| `eval_lambda` | — | coverage owner attribution via `decl_owner_file_set(decl_id, coverage_owner_file())` |
| `eval_call` | `try_force_any_deferred_for` lazy-module retry (both the plain-name and `Type.member` paths); enum-variant name validation | `host`/`gpu` lane calls via `eval_host_gpu_lane_call`; **implicit zero-arg `T__new` constructor dispatch** with recursion guard |
| `eval_function_call` | **value-type struct param copy-on-bind (#108)** — `interp_struct_is_value_type` / `val_struct_deep_copy` | function-scope **`defer`/`errdefer` execution** (depth tracking, tombstone trim); **argument write-back** for array/struct args bound to idents and field accesses |

Divergence runs in **both** directions on 8 of 10 pairs. There is no pair where
one side is a strict superset, so there is no safe blind merge and no pair was
merged.

## Real defects this implies (each needs its own verification)

1. **String interpolation drops literal segments.** The live
   `eval_interpolated_string` returns only the joined interpolated values.
2. **`defer` / `errdefer` never run at function scope** in this interpreter —
   the implementation exists only in the dead copy.
3. **`host` / `gpu` lane calls and implicit zero-arg constructors are dead.**
4. **Dict bracket-write (`d[k] = v`) via `val_struct_upsert_field` is dead** —
   and `dict_literal_dispatch_spec.spl` green-lights it by grepping for the
   source text of a function that never executes.
5. **Coverage owner attribution for lambdas is dead.**

## Corrected fix plan

1. **Do not delete either copy as a dedupe.** Any delete is a semantic change.
2. Treat each of the 10 as a genuine merge with a behavioural test written
   first. There is currently **zero behavioural coverage** for any of them —
   the four existing specs are source greps.
3. Replace the four grep-specs with specs that actually evaluate code, or mark
   them explicitly as structural-invariant pins so they are not mistaken for
   dispatch evidence again.
4. Only once each pair has a real oracle, fold the loser's unique behaviour into
   the winner (`eval_access.spl` / `eval_calls.spl`), and only then collapse the
   duplication — the winner is the file to keep, which is the opposite of the
   original plan.
5. Independently, fix the ordering hazard itself: the winner is decided by
   filename order within the package, which is not a stable contract.

## Prior work that remains valid

The 12 duplicates whose bodies were **byte-identical** can be removed safely
whichever copy wins. That change is unaffected by this finding.

Removed from `eval_access.spl`: `eval_array_lit`, `eval_tuple_lit`,
`eval_struct_lit`, `eval_compound_assign_expr`, `eval_return_expr`,
`eval_enum_variant_call`, `eval_enum_variant_access`, `eval_list_comp`,
`eval_dict_comp`.
Removed from `eval_calls.spl`: `parse_float_text`, `char_digit`,
`eval_struct_constructor`.

## Related

- `test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl`
- `test/01_unit/compiler/interpreter/dict_literal_dispatch_spec.spl`
- `test/01_unit/compiler/interpreter/text_byte_at_dispatch_spec.spl`
- `test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl`

All four pass (verified 2026-08-11, exit 0) and all four are source-text greps.
Their passing is **not** evidence about dispatch.
