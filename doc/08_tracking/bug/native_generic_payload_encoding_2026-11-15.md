# Native generic payload encoding: x8 / /8 across the erased-generic boundary (2026-11-15)

Status: M1 is fixed in MIR source on `work/native-generic-payload-encoding-20261115`.
M2 is fixed for free generic fns only; generic-class methods keep the
pre-fix behaviour (see M2). M3-M5 are documented below, not fixed. Native
confirmation needs a Stage 2 built from the branch tip.

## Convention (what the fix enforces)

Generics are one erased body per generic fn (owner decision 2026-10-31,
`50.mir/_MirLowering/function_lowering.spl` `lower_type` TypeParam arm).

- A **free generic fn** sees every `T` as a TAGGED runtime word. The CALLER
  encodes: `lower_call` boxes a value passed into a `T` slot
  (`switch_operators_calls.spl` `case HirTypeKind.Any | HirTypeKind.TypeParam`
  -> `box_runtime_value`); container elements (`[T]`, `Dict<K, T>` values) are
  tagged by the containers themselves. The CALLER also decodes: a bare `-> T`
  result is decoded at its consumer (`local_needs_erased_decode`,
  `mir_lowering_types.spl`), and now (M1) a `T` inside `T?` / `Result<T, E>`
  is decoded at the call boundary. Text handles, records and arrays keep one
  word either way; i64 (`<< 3`), f64 (heap box) and bool (11/19) do not.
  Inside a free body every `T` value is encoded, so a `Dict<K, T>` read
  keeps the stored word, as an array element read does.
- Concrete `T?` / `Result<T, E>` payloads are RAW (`Some(5)` ->
  `rt_enum_new(1, 0, 5)`; f64 is the bitcast bits).
- **Methods of a generic class** on the release tip have an UNTYPED symbol
  (the declared signature is not published in bootstrap mode), so arguments
  go in raw and results come out raw ("plain values in and out"), except a
  bare `-> T`, which the body re-boxes and the caller decodes. Inside a
  method a `T` value is therefore plain, and a `Dict<K, T>` read decodes.
- **Who writes what into a `Dict<K, T>`** (MIR dumps,
  `build/p3g4/conv/main.spl`): concrete code encodes on write
  (`rt_value_int_wide` then `rt_dict_set`). A free generic fn stores its `T`
  word, which the caller already encoded. A generic method stores its plain
  `T` argument RAW (`Bag.put(44)` passes 44 unencoded). Concrete code and
  free fns therefore agree with each other, and methods do not. No read rule
  can serve a method that reads both a concretely built dict (b08, which
  needs a decode) and its own writes (SparseHash, which needs none). Making
  the writers agree means encoding method `T` arguments at the call, which is
  the generic-method signature work in the sibling branch.

## M1: free generic `T?` / `Result<T, E>` payload never decoded

Minimal repro (`test/fixtures/native_generic_payload_encoding/free_fn_payload/main.spl`):

```
fn wrap<T>(x: T) -> Result<T, text>:
    Ok(x)
match wrap(7):
    case Ok(v): print v      # seed 7, native 56
```

`first<T>(xs: [T]) -> T?` gives the same (7 -> 56, 3 -> 24) with one OR two
instantiations (the "one element type prints 7" observation did not
reproduce on run-34 for `match first([7, 3])`). f64: llvm prints the heap
box pointer (`202412124828289.0`), cranelift refuses `main.f1` (verifier:
the Some arm copies the undecoded i64 word into the f64 merge local). bool
through `??`: prints `11`.

Cause: the caller boxes the argument (`rt_value_int_wide`), the body's
`Ok(x)` stores the tagged word, and the caller's match reads the payload as
the instantiated `Result<i64, text>` (raw). No site decoded a `T` nested in
an Option/Result.

Fix: `decode_erased_scalar_call_payload` (`switch_operators_calls.spl`),
called from the direct-call return of `lower_call`. When the callee's
declared return is `Optional(T)` / `Result(T, E)`, it binds `T` (and a bare
`E`) only from arguments whose word reaches the body encoded: a bare `T`
slot, a `[T]` element or a `Dict<K, T>` value. If `T` binds to an integer,
float or bool, it checks the Some/Ok variant at runtime
(`rt_enum_check_variant`), decodes the payload (`rt_value_as_int_wide` /
`rt_value_as_float` + bitcast / both bool encodings), REBUILDS the enum
(`rt_enum_new`; never mutates, the callee may return a stored box) and types
the result as the concrete instance. `enum_match_subject_type` accepts that
retained concrete instance of the expression's generic declaration. If any
parameter of the declared return stays unbound, there is no decode (the
pre-fix behaviour), and the code never builds a type that still holds an
unbound parameter (r07: `mk<T, E>`). A refusal cannot replace that skip.
When `T` is unbound, nothing proves it is scalar, and record or text
instantiations, which are right today, would be rejected.

Not touched: text/record/array instantiations, method calls of generic
classes, calls whose `T` is bound only by explicit type arguments or by a
generic-class argument (`Box<T>` fields are stored raw by construct sites).

### M1 follow-up: consumers that typed the payload as the declared `T`

A Stage 2 built from the first fix (d957f2b94dc) printed `j ok 1` for
`val v = nonempty([1, 7])?; Ok(v + 1)` (seed `ok 8`): 7 decoded twice
(`7 >> 3 = 0`, `+ 1`). Two consumers typed the payload from the callee's
DECLARED return and decoded again, which was right while the payload was
still tagged:

- `?` on a Result (`lower_try_expr`) decoded with the declared `Ok` type
  `T`. It now uses the concrete instance remembered on the call's result
  local when that local instantiates the declared type.
- `if val x = first([7])`: the binder keeps the declared `T` (decoded on
  use), and a raw i64 word cannot be told from the nil sentinel 3. The
  `.?` present edge re-tags an integer payload of a decoded generic call
  (`box_runtime_value`), so the nil test (`rt_native_eq`) stays real and
  `x` is decoded once on use.

Also: an arithmetic argument (`wrap(v + 1)`) now binds `T` (an untagged
I64/F64 arithmetic result is a raw scalar), so that call's payload is
decoded instead of read x8. Rows n-x of the fixture cover each consumer.

## M2: `Dict<K, T>` index read inside the erased body decodes `T`

Minimal repro (`test/fixtures/native_generic_payload_encoding/erased_dict_value/main.spl`,
trait-free copy of `AttributeStoreV1` placements): `self.hash[node]` in
`fn get(node) -> Result<T, text>` lowered to `rt_dict_get` +
`rt_value_as_int_wide`, so SparseHash read 9000000000 as 1125000000 and -5 as
-1, while Column (`Ok(v)` from `[T?]`) passed the word through.

Fix, limited to free generic fns: `lower_dict_runtime_read` (`expr_dispatch.spl`)
keeps the stored word on a bare `T` index read when the body is not a method
(`current_fn_is_method`, set by `lower_function`). The caller then decodes,
binding `T` from the `Dict<K, T>` argument (b05: `lookup_res(d, k)`). This
also fixes `lookup_or(d, k, fallback: T)`, which was wrong before the fix
(72): one body mixed a decoded read with an encoded fallback.

An UNANNOTATED or inline dict argument (`val d = {"a": 40}`,
`lookup_opt({"a": 40}, "a")`, a mutated `var d`) carries no element type
in MIR: no remembered HIR type, no expression type, no runtime element
type. `T` cannot be bound, and the 53b5f77ae5b Stage 2 printed 320 for 40
(b05u, f05, f04). For such a call, where `T` is unbound and the payload can
come from a `Dict<K, T>` argument, the caller applies the erased i64 decode
that the free body applied to the read before this branch. It keeps the
declared typing and marks, so the call behaves as it did before.

The first version of this fix kept the word in METHODS too. That broke b08
(`Bag.lookup` over a concretely built dict, 40 -> 320) and b05, so methods
are back to the pre-fix decode: their MIR is byte-identical to the
pre-branch source. The method-written SparseHash rows stay wrong, see the
Convention section and `known_wrong/main.spl`.

## Not fixed here

- M3: a generic-class method `-> T?` (`Box.read()`) passed straight into a
  concrete `i64?` parameter is wrapped in Some a second time: the untyped
  method's result carries the bootstrap-erased Int, so `ensure_option_handle`
  takes the static-scalar arm (p5 probe: `rt_enum_new(1, 0, <Box.read result>)`).
  The sibling branch `work/p3-generic-method-match-20261115` (34907e7ec8c)
  publishes the signature of generic-owner methods without a `T` parameter,
  which removes the wrap (verified in a seed MIR dump with both patches).
  Hazard in that branch: `fn at(i) -> T` becomes typed while `put(v: T)`
  stays raw, so the caller now decodes (`rt_value_as_int_wide`) a raw
  return: 42 -> 5.
- M4: module-level `match g.set(5): case Ok(b): print "set {b}"` (generic
  method, concrete `Result<bool, text>`) prints `set 1`; the same call inside
  a function prints `true`. A payload typing gap at module scope, not an
  encoding fault.
- M5: `if val r = <Result>.ok` on `Err` runs the Some branch with the nil
  word 3 (non-generic too). Owned by the sibling branch
  `work/p3-generic-method-match-20261115` (its bug note is not on this branch).
- M3 and M4 stay SILENTLY wrong here, by decision:
  - M3: a refusal IS feasible, because the callee is a known generic-owner
    method whose declared return is `T?`. `ensure_option_handle` itself
    cannot see that (the untyped result looks like an `i64` local), but
    the call site can. It was not added because the sibling's signature
    publication removes the double wrap and would have to undo a refusal.
    The sibling also still carries the `at() -> T` 42 -> 5 hazard. Owner
    call.
  - M4 is a module-scope typing gap (raw bool 1 printed for `true`), not
    an encoding fault. The compiler closure runs no module-level `match`
    on generic-method results. It needs its own repro and fix.
- Concrete (non-generic) `if val x = g()` with `g() -> i64?` folds the
  nil test (`x != nil`) away, so `None` takes the Some branch with the nil
  word 3. This is the M5 class. The decoded generic `if val` above is NOT
  affected, because its binder is tagged.
- `wrap(41).unwrap_or(-1)` on a free generic call fails MIR
  ("unsupported Result unwrap payload type: payload is other") before and
  after this fix.
- Wrong before AND after (`test/fixtures/native_generic_payload_encoding/known_wrong/main.spl`,
  MIR byte-identical to the pre-branch source): method-written SparseHash
  (9000000000 -> 1125000000), `first([[1, 2, 3]])` (r04, 0), `if val` over
  `pick<T>(o: T?)` (c03, 1), `apply(first, ..)` callback (56), generic method
  `-> T?` through `??` (b10, a pointer), `Box<text>.get()` into `wrap`
  (a pointer), `T` bound to an enum with payload (r03, panic),
  `wrap(b.get())` with `Box<i64>.get() -> T` (d04, 264: a method result
  carries no binding for `T`, so the payload is not decoded) and
  `lookup_res` over `Dict<text, Dict<text, i64>>` (e03, the inner read gives 0).

## Evidence

- Seed spec `test/01_unit/compiler/mir/native_generic_payload_encoding_spec.spl`:
  red 3/7 with the source change reverted, green 7/7. After the follow-up:
  red 10/13 against d957f2b94dc's source, green 13/13.
- Stage 2 from d957f2b94dc: erased_dict_value 6/6 rows match the seed on
  cranelift and llvm. free_fn_payload matched 12/13, failing on row j.
  Rows n-x are new and need the next Stage 2.
- Single-file bootstrap MIR lowering of `00.common/data/attribute_schema_v1.spl`
  and the 5 `test/fixtures/compiler/erased_generics/*` fixtures: error set
  byte-identical with and without the fix; `attribute_schema_v1_spec` 9/9.
- Independent review of 9810bad0cbc (fix Stage 2 vs run-34 Stage 2, both
  backends): b05 and b08 went right -> wrong (40 -> 320), r07 went right ->
  refused. Reproduced here; the probes are now fixture rows. After the
  rework, MIR per function compared with 9810bad0cbc changes only r07a,
  r07c and b05, plus the three methods, which are now byte-identical to the
  pre-branch source. `known_wrong` and `AttributeStoreV1` are byte-identical
  to the pre-branch source. Spec: red 12/17 -> green 17/17.
- Re-review of 53b5f77ae5b: b05u, f05 and f04 (unannotated or inline dict)
  went right -> wrong (40 -> 320), confirmed here on both backends. After
  the compat decode, per-function MIR against 53b5f77ae5b changes only those
  three functions, which now lower like the annotated b05 (right natively).
  Spec: red 17/20 -> green 20/20.
- Run-34 Stage 2 (red) on the fixtures: free_fn_payload llvm differs on rows
  a b c e f h i l m, cranelift build fails (verifier); erased_dict_value
  cranelift and llvm differ on the two hash rows.
