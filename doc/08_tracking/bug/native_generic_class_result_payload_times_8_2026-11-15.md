# Generic class Result payload read x8 / ÷8 when a generic-owner method symbol is typed (2026-11-15)

**Status:** both were introduced on branch `work/p3-generic-method-match-20261115`
(x8 by a13439c4680, ÷8 by its gated follow-up 34907e7ec8c) and are removed
there: the method symbol is no longer typed at all (approach A below). Confirmed
natively with a Stage 2 built from 20762e84620 (both fixtures equal the seed on
cranelift and llvm). The `.ok` + `if val`, f64, let-bound text and
array-stored rows are pre-existing and still open.

## Repro

- `test/fixtures/native_generic_method_result_match/` (must equal the seed)
- `test/fixtures/native_generic_method_result_let_bound/` (must equal the seed)
- `test/fixtures/native_generic_payload_encoding_known_wrong/` (known-wrong rows)

```
class Store<T>:            # impl Store<T>: fn get(node) -> Result<T, text>
var int_stores: [Store<i64>] = []
int_stores[0].set(2, 42)   # me set(node: i64, value: T)
match int_stores[0].get(2):
    case Ok(v): print(v)   # seed 42
```

## Evidence (aarch64, SIMPLE_BOOTSTRAP=1 native-build --entry-closure, whole program, no competing enum)

| row | seed | run 34 (43d59a39947) cl / llvm | c79c19e08c9 (typed symbol) | 34907e7ec8c (typed unless a param mentions T) |
|---|---|---|---|---|
| `match get(2)` after `set(2, 42)` | 42 | 42 / 42 | 336 / 336 | 42 |
| `?` then `"ok {v+1}"` | ok 43 | ok 43 / ok 43 | ok 337 / ok 337 | ok 43 |
| `val q = get(2); match q` +1000 | 1042 | 1042 / 1042 | 1042 / 1042 | **1005** |
| construct-site `Store(slots: [Some(4)])` | 4 | 4 / 4 | 4 / 4 | 4 |
| `if val r = get(2).ok` | 42 | 0 / 4 | 336 / 336 | - |

## Consumer conventions (one erased body per generic method)

A `T` inside the erased body is whatever word the caller passed. "Untyped" is
the generic-owner method symbol in bootstrap mode before this branch
(`module_declarations_bootstrap.spl`, `impl_.type_params.len() == 0` gate).

| consumer of `get` / producer for `set` | untyped symbol (run 34, and approach A) | typed symbol (x8 / ÷8 builds) |
|---|---|---|
| `set(value: T)` argument, i64 / bool | raw word | i64 boxed `rt_value_int_wide` (`TypeParam` arg arm, ~9468); bool not measured |
| `set(value: T)` argument, text | pointer | pointer (no change measured) |
| `set(value: T)` argument, f64 | cranelift refuses: E-BACKEND-CRANELIFT-CALL-ABI | `rt_value_float`; read back as a denormal |
| direct `match get(i)` Ok payload, i64/bool/text | raw read | raw read, so boxed args read x8 |
| `val q = get(i); match q` | raw read (i64/bool ok; text prints an integer, pre-existing) | decodes the payload, so raw-stored values read ÷8 |
| `get(i)?` | raw | raw (x8 with boxed args) |
| passed to a call / returned | raw (== seed) | not measured separately |
| stored in an array then matched | aborts "total enum match fell through on 'Result'" (pre-existing) | not measured |
| `.ok` + `if val` | wrong: `.ok` is payload-or-nil-word, `if val` is constant-true (pre-existing, also non-generic) | wrong |
| `.unwrap_or` | run 34 cannot build it from this shape ("unresolved method call") | not measured |

Mixing the two columns in one program is what produced x8 and ÷8.

## Fix (approach A)

Nothing is typed. `enum_match_declared_owner_key`
(`50.mir/_MirLoweringExpr/switch_operators_calls.spl`) is consulted only when
the bare-variant owner search is already ambiguous: for a method-call subject
it looks up the callee's declared return (receiver's declared type, or the
declared element type of an index receiver -> `lookup_method_in_type` ->
`resolved_call_hir_return_type`) and keeps the Result/Option owner. The
subject's type and the payload bind are the same as on the unambiguous path.
The spec `generic_method_result_match_subject_spec` asserts per-function MIR
identity against the program without the competing Ok/Err enum, and that no
i64 path calls `rt_value_int_wide` / `rt_value_as_int_wide`.

## Still open

- A let-bound subject (`val q = s.get(i); match q`) is a local whose type is
  erased under SIMPLE_BOOTSTRAP=1, so its bare arms stay ambiguous when
  another enum declares `Ok`/`Err`.
- A same-module generic-owner method has no declared return under
  SIMPLE_BOOTSTRAP=1 (symbol untyped, `HirFunction.return_type` erased).
- A competing `Some`/`None` enum puts `Option` in `enum_bare_name_collisions`,
  which drops the total-match trap block (existing policy, not this fix).
- The pre-existing rows in the known-wrong fixture.
