# Interpreter: 10 drifted duplicate function definitions — the STALE copies WIN

Status: **OPEN (P2) — divergence confirmed still present; NOT a silent-wrong-result row**
Re-verified 2026-08-17 (wave_01 lane B). All five implied user-facing defects were
already probed and DISPROVED (see below); this pass found no new user-facing symptom
and made no code change. Routing note added — see "Lane routing" below.

## 2026-08-17 re-verification (wave_01 lane B)

Content check, current source:

- Both duplicate modules still exist: `src/compiler/10.frontend/core/interpreter/eval_access.spl`
  and `.../eval_calls.spl`. The divergence is NOT stale — the delete is still forbidden
  and the load-order question is still open.
- The path exclusion is still live at TWO sites, not one:
  `src/compiler/80.driver/driver_source_loading.spl:868` and `:903`
  (`p.contains("/core/interpreter/")` in both).

**Lane routing.** This row was sliced to lane B on the strength of its `file` column
(`80.driver/driver_source_loading.spl`), but the defect and its fix both sit in
`10.frontend` — the doc's own `**Layer:**` field says so, and the divergent definitions
are all under `10.frontend/core/interpreter/`. `10.frontend` is claimed by another lane,
so lane B did not edit it. Whoever owns `10.frontend` should take this: the exclusion
lines above are the 80.driver-side lever, and they are the only part of the fix that
lands outside `10.frontend`.

**Severity framing.** This does not belong in the "silently wrong results" batch. The
premise "the STALE copies WIN and therefore users get wrong answers" was falsified by
the second pass (five defects probed, all disproved) and the third pass retracted the
unreachability claim in the other direction. What is left is a real but *latent*
maintenance hazard: two divergent definitions where the winner is decided by load order
rather than by intent.
**Filed:** 2026-08-11
**Updated:** 2026-08-11 (resolution winner measured; original premise falsified)
**Updated:** 2026-08-11 (second pass: all five implied defects disproved by
measurement; root cause thought to be a build exclusion in `_driver_collect_sources`)
**Updated:** 2026-08-11 (third pass — **RETRACTION**, see below)

## RETRACTION: "the whole package is excluded from the build" is FALSE

The earlier claim in this file that the package is "excluded from the build, so
both copies are unreachable" is **withdrawn**. It generalised from one direct
call to `_driver_collect_sources` to all build lanes, and that does not hold:

- Specs `enum_bare_name_collision_dual_key_spec.spl` and
  `compiled_module_adapter_spec.spl` **execute** functions defined ONLY inside
  this package (`enum_table_register`, `cmr_register` — single definitions, no
  shadows) and pass 9/9 each with implementation-specific semantics.
- `80.driver/driver_source_loading.spl:15` and
  `50.mir/_MirLowering/module_lowering.spl:65` import `hm_hash_text` from it.
- `_driver_collect_sources` is itself **duplicated** — the copy at
  `80.driver/driver_helpers.spl:84` carries **no** `/core/interpreter/`
  exclusion — so the probe measured an ambiguous winner, not the build.

The divergence table below remains valid and the delete remains forbidden; only
the unreachability conclusion is retracted. Severity is latent-but-live, not
dead. Full evidence and the retire/reconnect decision:
`doc/08_tracking/bug/driver_collect_sources_path_exclusions_are_not_dead_code_2026-08-11.md`
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

## Real defects this implies — ALL FIVE DISPROVED (2026-08-11, second pass)

The five hypothesised user-facing defects below were each probed empirically.
**None reproduces.** The premise they all rest on — that the winning copy is on
a user-facing execution path — is false.

### Root cause of the disproof: the ENTIRE package is excluded from the build

`_driver_collect_sources` (`src/compiler/80.driver/driver_source_loading.spl`,
lines 858 and 893) unconditionally drops every path containing
`/core/interpreter/`, in **both** the single-file branch and the directory-walk
branch:

    if p.contains("/core/interpreter/") or ... : return result

Measured directly by calling the function, with a positive control:

| path | files collected |
|---|---|
| `.../core/interpreter/eval_access.spl` (the "winner") | **0** |
| `.../core/interpreter/_EvalOps/access_literal_assign_eval.spl` (the "loser") | **0** |
| `.../10.frontend/core/lexer.spl` (CONTROL) | **2** |

So *neither* copy is compiled into any built `simple` binary. The winner/loser
distinction established on 2026-08-11 is real as source drift, but it decides
which of two **equally unreachable** functions a hypothetical build would pick.
Corroborating: `grep -rn 'core_interpret\b' src/` returns hits only inside the
package itself — the package's own entrypoint has **zero external callers**, and
the only cross-package import of it anywhere is
`compiler.core.interpreter.hashmap.{hm_hash_text}`.

A `strings`-based symbol probe on `bootstrap/stage3/simple` was also run and
returned 0 for every interpreter symbol — **that probe is vacuous and is not
cited as evidence**: its positive controls (`_driver_collect_sources`,
`parse_expr`) also returned 0 because the binary is stripped.

### Per-defect verdicts (engine stated for each)

1. **String interpolation drops literal segments — NOT REPRODUCED.**
   `print("a{x}b")` with `x = 42` prints `a42b` under both `bin/simple run`
   (Cranelift JIT) and `SIMPLE_NO_JIT=1 bin/simple run` (tree-walk). The live
   `parts.join("")` reads wrong against `expr_interpolated_string`'s contract
   (args = only the `{...}` part exprs; the verbatim template lives in the str
   slot), so the *code* is genuinely wrong — but it never executes.
2. **`defer` / `errdefer` never run — NOT REPRODUCED.** A function-scope
   `defer print("DEFER-RAN")` runs, printing `BODY` then `DEFER-RAN`, on both
   engines.
3. **`host` / `gpu` lane calls and implicit zero-arg constructors dead — NOT
   REPRODUCED as a user-facing defect.** Same build exclusion; the shipped
   engines implement these on their own paths.
4. **Dict bracket-write dead — NOT REPRODUCED.** `d["b"] = 2` on a dict literal
   reads back `2` on both engines. The criticism of
   `dict_literal_dispatch_spec.spl` still stands on its own terms: it is a
   source grep and proves nothing either way.
5. **Coverage owner attribution for lambdas dead — NOT REPRODUCED** as a
   user-facing defect, for the same build-exclusion reason.

### What the actual defect is

Not any of the five. It is that **~100 KB of drifted, self-contradictory
evaluator source is retained in-tree while being hard-excluded from the build by
a path substring in the driver**, with four source-grep specs giving it the
appearance of live coverage. The decision to make is retire-or-reconnect, and
until it is made no merge work on the 10 pairs buys any user-visible behaviour.

### Engines that DO serve users

`bin/simple` is the **Rust seed** (it says so on startup). `bin/simple run` is
Cranelift JIT, `SIMPLE_NO_JIT=1` is the seed's tree-walk interpreter, and
`bootstrap/stage3/simple` offers only `compile` / `native-build` — it has no
interpreter subcommand at all (`run`, `interp`, `eval`, `exec` are all
`unknown command`). None of them routes through this package.

## Corrected fix plan (revised again after the disproof)

**Severity is now LOW-and-latent, not user-facing.** The merge work described
below buys zero user-visible behaviour while the build exclusion stands, so the
exclusion decision comes first.

1. **Decide retire-or-reconnect for the whole package.** Either delete
   `src/compiler/10.frontend/core/interpreter/` (keeping `hashmap.spl`, its one
   externally-imported module) and drop the `/core/interpreter/` clause from
   `_driver_collect_sources`, or reconnect it and give it an entrypoint. Do not
   do merge work before this is decided.
2. **Do not delete just one copy as a dedupe.** If the package is reconnected,
   any single-copy delete is a semantic change (the 10-pair table above).
3. **No new behavioural specs against this package** until it is reconnected —
   a spec that cannot execute the code under test is another fake oracle, which
   is the failure mode this filing exists to document.
4. The four grep-specs should be explicitly relabelled as structural-invariant
   pins, or deleted with the package. They must not be cited as dispatch
   evidence again.
5. Independently, the ordering hazard (winner decided by filename order within a
   package) is a real language/resolution defect and is worth its own filing —
   it is not specific to this package and would bite any reconnected one.
6. **Do not "fix" `parts.join("")` in isolation.** It is genuinely wrong against
   `expr_interpolated_string`'s contract, but patching unreachable code produces
   an unverifiable change; fix it as part of step 1 if the package is kept.

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

## Verification 2026-08-17 (w0001 compiler_spl lane)

Two corrections to how this row is being tracked:

1. **The silent-wrong-result premise is falsified by the doc's own body** (line 28):
   "the STALE copies WIN and therefore users get wrong answers" — falsified. The row
   should therefore not be carried in the silently-wrong-results batch; it is a
   maintainability/drift row (~100 KB of self-contradictory duplicated source), which
   is what the doc actually concludes.

2. **The row's `file` column points at the wrong file.** It names
   `src/compiler/80.driver/driver_source_loading.spl`, which contains **no** `eval_access`
   reference (`grep -n "eval_access\b"` on it is empty). The duplicated modules the doc
   discusses live under `src/compiler/10.frontend/core/interpreter/` — a lane claimed by
   another session. Left untouched here for that reason.

The doc's own instruction "DO NOT DEDUPE — needs a load-order fix, not deletion"
is respected: no source was changed.
