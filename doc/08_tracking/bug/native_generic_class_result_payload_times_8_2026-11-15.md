# Generic class Result payload read x8 after a `T` argument is boxed (2026-11-15)

**Status:** the x8 on `match`/`?` was introduced by a13439c4680 and is fixed on
the same branch (`work/p3-generic-method-match-20261115`) by gating the HIR hunk;
needs a new Stage 2 to confirm natively. The `.ok` + `if val` and f64 rows are
pre-existing and still open.

## Repro

`test/fixtures/native_generic_method_result_match/` (must equal the seed) and
`test/fixtures/native_generic_payload_encoding_known_wrong/` (known-wrong rows).
Minimal shape:

```
class Store<T>:            # impl Store<T>: fn get(node) -> Result<T, text>
var int_stores: [Store<i64>] = []
int_stores[0].set(2, 42)   # me set(node: i64, value: T)
match int_stores[0].get(2):
    case Ok(v): print(v)   # seed 42
```

## Evidence (aarch64, SIMPLE_BOOTSTRAP=1 native-build --entry-closure, whole program)

No second enum declares `Ok`/`Err`, so the old compiler can lower the match.

| row | seed | old Stage 2 (run 34, 43d59a39947) cl / llvm | Stage 2 of c79c19e08c9 cl / llvm |
|---|---|---|---|
| `match get(2)` after `set(2, 42)` | 42 | 42 / 42 | 336 / 336 |
| `?` then `"ok {v+1}"` | ok 43 | ok 43 / ok 43 | ok 337 / ok 337 |
| let-bound `val q = get(2); match q` +1000 | 1042 | 1042 / 1042 | 1042 / 1042 |
| construct-site `Store(slots: [Some(4)])` then `match get(0)` | 4 | 4 / 4 | 4 / 4 |
| `if val r = get(2).ok` | 42 | 0 / 4 | 336 / 336 |
| `if val r = get(3).ok` (Err) | -3 | 0 / 4 | 3 / 3 |

## Mechanism

- Before a13439c4680 a generic-owner method symbol was untyped in bootstrap
  mode (`module_declarations_bootstrap.spl`, `impl_.type_params.len() == 0`
  gate). Callers therefore passed a `T` argument RAW, the erased body passed
  it through to `Ok(v)`, and the caller read the Ok payload raw. That was
  consistent, so the values came out right.
- a13439c4680 published the method's declared signature on its symbol
  (`declaration_lowering.spl`, generic-owner arm). For `set(value: T)` the call
  site then takes the `TypeParam` argument arm in
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl` (~9468,
  `box_runtime_value`, emits `rt_value_int_wide` / `rt_value_float`). The erased
  body stores and returns that tagged word unchanged. The Ok-payload bind
  for the RTI-substituted `Result<i64, text>` (`enum_payload_value`, raw read
  for i64, `Bitcast` for f64) never removes the tag. 42 << 3 = 336.
  Construct-site instances store raw, so one store can hold both encodings.
  The comment at ~8284 of the same file already names this hazard for struct
  fields.
- Fix on the branch: publish the signature only when no parameter mentions a
  type parameter. `get`, `has` and `len` are typed. `set(value: T)` stays
  untyped, so its arguments pass raw again. The spec
  `generic_method_result_match_subject_spec` asserts that the `put(value: T)`
  caller has no `rt_value_int_wide`.

## Still open (pre-existing)

- `if val r = <Result>.ok` for ANY typed Result, including a non-generic
  one: old Stage 2 prints `42 | 3` for Ok/Err (seed `42 | -3`). The `.ok`
  field lowers to payload-or-nil-word (`result_unwrap_mismatch` yields the
  constant 3) and `if val` emits a constant-true condition with no
  `rt_is_some`.
- f64 through `Store<f64>`: old cranelift rejects `set(1, 2.25)` with
  E-BACKEND-CRANELIFT-CALL-ABI (f64 argument to a callee with an unknown
  signature). With the boxed ABI, c79c19e08c9 read a denormal.
- A method that takes a `T` parameter and returns `Result<T, E>` still has
  no declared return in bootstrap mode, so a bare `Ok` arm over its result
  stays ambiguous.
