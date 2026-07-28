# Dict Iteration Order

**Contract: `Dict` iterates in SORTED key order (lexicographic by the internal
key string), on every engine, on every run.**

This applies to every order-visible dict operation:

| Form | Order |
|------|-------|
| `d.keys()` | sorted by key |
| `d.values()` | sorted **by key** (so `keys()[i]` pairs with `values()[i]`) |
| `d.entries()` / `d.items()` | sorted by key |
| `for (k, v) in d` | sorted by key |
| `print(d)` / `d.to_string()` | sorted by key |

Do NOT rely on insertion order. `{"b": 1, "a": 2}.keys()` is `["a", "b"]`.

## Why this contract

The interpreter backs `Value::Dict` with Rust's `std::collections::HashMap`,
whose `RandomState` hasher is **seeded per process**. Iterating it directly
produced a different key order on every run of the *same binary* over the *same
input*: a 4-key literal yielded **15 distinct orderings across 20 runs**. Any
spec asserting key order was therefore inherently flaky — green locally, red in
CI, with no code change in between.

Sorted order was chosen over the two alternatives:

- **Insertion order** is what most users expect from a dict literal, but it is
  not achievable across all backends. The compiled runtime's `RuntimeDict`
  (`src/compiler_rust/runtime/src/value/dict.rs`) is an open-addressing table
  that stores entries at `hash % capacity`, so it does not retain insertion
  order and could not without being rewritten. Adopting insertion order would
  have left the interpreter and the compiled path permanently divergent.
- **Explicitly unspecified** keeps the flakiness and just forbids testing it.

Sorted order is a pure function of key content, so *every* backend can produce
it identically without sharing a container — that is the property that makes
cross-engine agreement achievable at all.

It is also what this codebase already does elsewhere for exactly this bug class:
`Value::to_key_string` sorts struct field names before formatting, and the SFFI
externs `rt_dict_keys_fn` / `rt_dict_values_fn`
(`src/compiler_rust/compiler/src/interpreter_extern/sffi_dict.rs`) already
sorted their output.

## Implementation

One helper is the single source of truth:

```rust
// src/compiler_rust/compiler/src/value_impl.rs
pub fn dict_entries_sorted(map: &HashMap<String, Value>) -> Vec<(&String, &Value)>
```

Every order-visible dict boundary routes through it:

- `interpreter_method/collections.rs` — `keys`, `values`, `entries`/`items`
- `interpreter_helpers/collections.rs` — `for (k, v) in dict`
- `interpreter_call/block_execution.rs` — module-scope `for` over a dict
- `value_impl.rs` — `to_display_string`, `to_debug_string`

**If you add a new dict-iterating operation, route it through
`dict_entries_sorted`.** Sorting only some of these desyncs `keys()[i]` from
`values()[i]`, which is worse than the original bug.

## Known divergence: the compiled/JIT path (unfixed)

The interpreter now satisfies this contract. The Cranelift JIT / native path
does **not** yet: it iterates `RuntimeDict` in FNV-bucket order. That order is
*deterministic* (the hash is unseeded FNV-1a, so it is stable run-to-run), but
it is not sorted, so the two engines disagree:

```
d = {"a":1,"b":2,"c":3,"d":4}
SIMPLE_EXECUTION_MODE=interpret  ->  keys=abcd   (sorted, correct)
SIMPLE_EXECUTION_MODE=jit        ->  keys=cdab   (FNV-bucket, stable)
```

Closing this requires sorting the collected keys in `dict_collect`
(`src/compiler_rust/runtime/src/value/dict.rs`), which backs `rt_dict_keys`,
`rt_dict_values`, and `rt_dict_entries`. Note that the JIT path has a second,
independent defect in this area — `values()` returns corrupt payloads and
`print(d)` renders a raw pointer (`<dict@0x...>`) — so that work should be
scoped together with the existing native-dict bugs rather than as an
ordering-only change. See `doc/07_guide/language/dict_native_pitfalls.md`.

Until then: **do not write specs that assert dict order and run them on both
engines.** Order-independent assertions (`len()`, `has()`, sums) are safe
everywhere.
