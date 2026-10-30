# pure_sql native MIR failures (Phase 3 run-27e)

Status: source workarounds landed; compiler fix for cause 1 committed separately
(takes effect when the Phase 3 compiler rebuilds itself); causes 2 and 3 are open
compiler bugs.

Modules (`lib.nogc_sync_mut.database.pure_sql._PureDatabase.*`):

| module | run-27e error (fatal MIR items) |
|---|---|
| `row_value_helpers` | `unresolved method call: slice` x7 (706/714/716/734/739/741/777) |
| `pure_database` | `array return record element has no unique provider layout: lib.nogc_sync_mut.database.sql.types::DbValue` x3; `missing native trait implementation: ...PureDatabaseBitmapReducerV1 for ` (empty owner) x2 (lines 90:36, 3374:25) |

The `non-exhaustive enum match ... placeholder 0` items in the same lists are not
fatal (row_value_helpers links with six of them) and are not addressed here.

`lib.nogc_sync_mut.database.pure_sql.database` and
`lib.nogc_async_mut.database.sql.types` were "objectless" in run-27e only because
they are pure `export use` facades: the build log reports `funcs=0` for both, so no
object is emitted. Both build rc=0 with Stage 2 once `pure_database` lowers.

## Cause 1 — enum call result taints a `[DbValue]` (pure_database x3)

Reproducer (fails on Stage 2, any module):

```simple
var arr: [DbValue] = []
arr.push(_expr_to_dbvalue(e, params))   # direct call returning the ENUM DbValue
arr[k].is_null()                        # -> fatal "no unique provider layout"
```

Pushing a literal (`DbValue.Null`) or reading through a parameter passes. Binding
the result first (`val v: DbValue = ...; arr.push(v)`) and reading back from a
record field (`Cell(value: call()).value`) both still fail.

Mechanism: the MIR prescan registers a return shape via `composite_layout_key` for
every `Named` return type, enums included (`module_lowering.spl` Named arm of the
prescan; `declaration_providers_v1.spl` same). `remember_call_hir_return`
(`expr_dispatch.spl`) turns that into `struct_value_syms[call_local]`, and
`note_container_elem_type` copies the value's owner into
`array_element_struct_syms[array]` on push. The next index read runs
`checked_array_record_layout`, which is fail-closed for an owner with no record
layout — an enum has none. The three sites were the primary-key reads in
`_do_insert` (2) and `_do_insert_or_replace` (1).

The earlier theory in this lane ("a function returning `[DbValue]` fails") was
wrong: rewriting every `_deserialize_row` / `_copy_values` call site left the
count at exactly 3. Those edits were dropped.

- Workaround (tagged `@workaround`): read the three cells through
  `_dbvalue_at(values, index)` (row_value_helpers), whose parameter carries no taint.
- Compiler fix (separate commit): `note_container_elem_type` no longer copies an
  owner into `array_element_struct_syms` when it positively names an enum (no
  record layout in `struct_field_order`, and present in the qualified or
  unambiguous bare enum variant index). An owner whose record layout is simply not
  demanded yet keeps its element owner, so struct-array decoding is unchanged. The
  value's own `struct_value_syms` is untouched, so enum-equality dispatch that
  reads it is unaffected. Not yet exercised by a rebuilt compiler.

## Cause 2 — `Some(<trait value>)` / trait field read into a constructor (open)

`coerce_native_trait_object` (`native_trait_conversion.spl`) finds no concrete owner
when the value is already a trait object whose local carries no HIR type: the
`if val Some(strategy) = reducer` binding re-wrapped as `Some(strategy)`, and the
field read `reduced.reducer` passed to a constructor (a typed `val x: Trait = ...`
does not help). It then searches for an implementation for the empty owner and
fails. A value whose HIR type is already the expected trait should be identity.

- Workaround (tagged): `_PureDatabaseReducerSlotV1` boxes the reducer so the Option
  payload is a record, and the new reducer is taken from a `match` result, which
  carries a concrete owner.

## Cause 3 — flow-narrowed two-hop read loses `text` (open)

`val expr = where_expr` after `if not where_expr.?` and `expr.right.value` after
`if not expr.right.?`: the native MIR gives `pattern` no type, so `pat.slice(...)`
is unresolved.

- Workaround (tagged): annotate `val pattern: text` / `var pat: text`. The field is
  declared `value: text`, so this narrows nothing that could be nil.

## Evidence

- Bisection: four-way then per-method split of `pure_database` into probe modules
  compiled with the Stage 2 `S/r27/stage2-simple` native-build (go-to-end), then
  single-pattern probes (r1-r5, c1-c4) as above.
- After the workarounds: `pure_database`, `row_value_helpers`, `pure_sql.database`
  entries build and link rc=0 with Stage 2.
- Semantics: `test/02_integration/lib/database/pure_sql_native_mir_regression_spec.spl`
  (auto INTEGER PRIMARY KEY, INSERT OR REPLACE, LIKE prefix/suffix) 3/3 pass in the
  interpreter.
