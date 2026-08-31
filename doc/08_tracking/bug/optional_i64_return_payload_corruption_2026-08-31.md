# `i64?` return payload is silently corrupted (seed interpreter)

Status: OPEN — SILENT WRONG ANSWERS, no error raised
Found: 2026-08-31, while applying the class-(c) optional-widening remedy to
`ThreadHandle.join()` (known_bugs C12).
Severity: high. This produces wrong numbers rather than failing.

## Reproduce

```simple
fn f() -> i64?: 42

fn main():
    val v = f()
    print("raw: {v}")                       # expected 42
    if v != nil:
        print("plus1: {v + 1}")             # expected 43
    val d = f() ?? 0
    print("coalesce: {d} plus1: {d + 1}")   # expected 42 / 43
```

Actual, on the Rust seed (`bin/simple run`):

```
raw: 0.000...0002        # a denormal float, not 42
plus1: <special:5>
coalesce: 0.000...0002  plus1: <special:5>
```

Every line is wrong and nothing faults. The payload is already corrupt at the
point of return — before any arithmetic — so the value is being boxed as a
float / NaN-tagged value and read back with the wrong tag.

`?? 0` does NOT rescue it: coalescing yields the same corrupt payload, so
there is currently no idiom that recovers an `i64` from an `i64?`.

## `Any?` is wrong too, differently

```simple
fn g() -> Any?: 7
# guarded `a + 1` prints 1, expected 8
```

Also silently wrong, but not a denormal — a different miscomputation.

## Scope — what still works

The **extern-backed** path is unaffected. `std.concurrent.thread`'s
`ThreadHandle.join() -> i64?` (widened in the same change) round-trips a real
i64 correctly; this is pinned by the second example in
`test/01_unit/std/concurrent_join_nil_contract_spec.spl`. Only a Simple-level
function returning an optional literal was observed corrupting.

## Why this matters beyond one bug

The project's documented class-(c) remedy for
`nil is forbidden by the non-optional return contract` (see
`test/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.spl`)
is to widen the declaration `T -> T?`. For NUMERIC `T` that remedy is
currently unsafe: it silences the contract fault and replaces it with a
silently corrupt value. Widening an `i64`-returning function should be
treated as blocked until this is fixed.

This also blocks 4 examples in `test/01_unit/std/perf_optimization_spec.spl`
that accumulate `total + handle.join()` / `sum + ch.try_recv()`, which fail
with `type mismatch: cannot convert enum to int` once the declarations are
widened — including one site (line 348-350) that already nil-guards, i.e. the
guard does not narrow.

## Not attempted here

The fix is in the seed's optional value representation
(`src/compiler_rust/compiler/src/...`), which is a compiler design decision and
out of scope for a stdlib bugfix.
