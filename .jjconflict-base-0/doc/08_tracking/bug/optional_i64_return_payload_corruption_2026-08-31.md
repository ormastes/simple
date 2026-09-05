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

## Resolution — consumer half (2026-08-31, fix/optional-narrowing-divergence)

PR #138 fixed the producer (tail-return boxing). This change fixes the
CONSUMER half plus the lane divergence:

1. **Unwrap idioms now yield the raw payload on the JIT lane** (interpreter was
   already correct). `f() ?? d` (hir `lower_coalesce`), `if val n = f():`
   (`build_if_let_binding_stmts`) and `f().unwrap()` are typed as the raw
   inner scalar when the subject is `T?` over a BoxInt-family scalar
   (i8..i64, u8..u32), and mir `lower_builtin_call_expr` unboxes
   `rt_unwrap_or_self` by name+type — the same mechanism `rt_enum_payload`
   already had. Before: `(f()??0)` printed 336 (= 42<<3), `+1` gave 337,
   `.unwrap()+1` 337, `if val n: n+1` 337. After: 42/43 on both lanes.
   Probe: `test/01_unit/compiler/interpreter/probe_optional_unwrap_idioms_jit.spl`
   (4 FAILURES on the pre-fix binary, ALL PASS after, both lanes).

2. **Arithmetic on an UNNARROWED optional now fails closed on the JIT lane
   too.** `if v != nil:` does not narrow (flow_sensitive_narrowing_design.md
   is a PROPOSAL, not implemented); the interpreter faulted at runtime while
   the JIT silently computed `42 << 3 = 2688` on the tagged bits. HIR
   `lower_binary` now rejects arithmetic/bit/shift/ordered-compare when an
   operand is an optional BoxInt-family scalar, with a message naming the
   working idioms. Eq/NotEq/Is (nil checks) stay allowed. Both lanes now end
   in the same "cannot convert enum to int" interpreter fault for the R2
   repro.

Deliberately NOT covered (unchanged behavior, representations are
asymmetric): `u64?` (HeapUInt), `f64?`/`f32?` (raw enum payload bits vs
BoxFloat), `bool?` (rt_value_bool), and `Any?` (known_bugs R4). Whether
`!= nil` should narrow remains the design decision tracked by the PROPOSAL
doc — narrowing was not invented here.
