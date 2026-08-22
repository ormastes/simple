# `self.field.push(x)` inside a `me` method deep-copied the array on EVERY call (seed interpreter)

**Status:** FIXED 2026-08-22 (seed interpreter, `src/compiler_rust/compiler`).
**Class:** value-semantics COW + accidental aliasing = O(n) per write
(`doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`, shape (d)),
but on the `me`-method receiver path, which the 2026-08-21 `obj.field.push` fix did not cover.

## Symptom

Any accumulation through a mutating method on a local object is quadratic under
`SIMPLE_EXECUTION_MODE=interpret` (and on every interpreter-fallback function under the JIT):

```simple
class Counter:
    hist: [i64]
    me bump(v: i64):
        self.hist.push(v)      # O(len) per call

var c = Counter.new()
while k < n:
    c.bump(k)                  # whole loop O(n^2)
```

| pushes | pre-fix wall (seed, interpret) | post-fix |
|---|---|---|
| 2,000 | 0.04 s | 0.02 s |
| 4,000 | 0.13 s | — |
| 8,000 | 0.46 s | — |
| 16,000 | 1.50 s (x3.3 per doubling = quadratic) | 0.09 s |

Mechanism counters (new, `SIMPLE_PERF_COUNTERS=1`): 2,000 pushes →
`SELF_FIELD_ARR_COW_CLONES` **2000** pre-fix, **0** post-fix. Cargo pin
`me_method_self_field_push_scales_linearly`: x4 pushes cost **x17.5** pre-fix, **x3.9** post-fix.

## Mechanism

`interpreter_helpers/patterns.rs` (identifier receiver, method found on the class) takes the
receiver OUT of the env so the callee owns it ("zero-copy"), but then immediately re-inserts an
`Arc::clone` of the field map so the call's arguments can still read `c`:

```rust
if let Some(Value::Object { class, fields }) = env.remove(obj_name) {
    env.insert(obj_name, Value::Object { class, fields: Arc::clone(&fields) });   // refcount 2
    find_and_exec_method_with_self_owned(..., fields, ...)
```

The alias lived for the whole call. Inside the body `self.hist.push(v)` reaches
`try_field_array_mutation_in_place`, whose `Arc::make_mut(fields)` shallow-copies the field map
(refcount 2) and whose `Arc::make_mut(array)` then finds the array Arc shared between the two
maps and deep-copies the `Vec<Value>` — every call, whole array. The existing
`ARR_MUT_COW_CLONES` counter never saw it because that counter only instruments the
identifier-receiver path (`arr.push(x)`), not the object-field path.

## Fix

`interpreter_method/special/execution.rs::exec_function_with_self_return` takes
`release_receiver: Option<&str>`. After `bind_args` has evaluated the arguments (so
`c.bump(c.count)` still works) and before the body runs, if the caller's binding still holds the
same field map (`Arc::as_ptr` equality), it is removed from the caller env for the duration of
the body. `self` is then the unique owner and every in-place mutation path stays in place. The
caller already rebinds the name from the returned `updated_self`; on an error the receiver is
put back so a caught error still sees the binding.

Value semantics are unchanged: any OTHER holder (`val snapshot = c`, a captured closure, an
array element) keeps its own Arc, so `Arc::make_mut` still copies exactly when something else can
observe the object (`aliased_receiver_still_copies_on_write` pins this).

Also in this change: `node_exec.rs` no longer clones the `Type` annotation of every
`let`/`val`/`var` statement on each execution (it was only ever read by reference).

## Reproduce / pin

- `src/compiler_rust/compiler/tests/interpreter_me_method_field_push_in_place.rs` — counter pin
  (0 COW clones over 2,000 pushes; 2,000 pre-fix), linear-scaling pin (ratio < 9; 17.5 pre-fix),
  aliasing and argument-order semantics pins.
- `scripts/check/check-perf-regression-tests.shs` row `me-method receiver released`.
- Counters: `SELF_FIELD_ARR_MUT_CALLS`, `SELF_FIELD_ARR_COW_CLONES`, `SELF_FIELD_ARR_COW_ELEMS_CLONED`.

## Wider effect

`bin/simple run` (interpret) of a 1.8k-line interpreter-heavy program
(`22 x {array/dict/text/struct/enum/closure/me-method}` families, n=3000): 4.65 s → see commit
message for the post-fix figure measured on the same binary pair.

Measured on `/mnt/data/seedperf/mut_6000.spl` (n=6000, interpret), `simple.base` vs `simple.fix1`:

| op | base | fix-1 |
|---|---|---|
| `self.names.push` | 1040 ms | 478 ms |
| `self.surfaces.push(struct)` | 3487 ms | 231 ms |
| `self.dict[k]=v` | 3451 ms | 182 ms |
| whole program | 9.34 s / 30.3 MB | 1.70 s / 31.7 MB |

## Superseded mechanism (2026-08-22, rebase note)

While this was being measured, `f8681a7afa6` (another lane,
`interpreter_me_call_dict_clone_2026-08-22.md`) landed the same defect class by a different
mechanism: arguments are evaluated first (`evaluate_call_args`) and the receiver is MOVED into
the callee, so no alias ever exists. The `release_receiver` path described above was therefore
dropped before landing. What lands here: the `SELF_FIELD_ARR_*` counters, the four-test cargo
pin (which passes unchanged on `f8681a7afa6`: 0 clones / 2,000 pushes; linear scaling),
the `let` Type-annotation clone removal in `node_exec.rs`, and the perf-regression gate row.
