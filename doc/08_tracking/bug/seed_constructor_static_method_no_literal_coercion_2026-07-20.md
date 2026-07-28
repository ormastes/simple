# Bug: seed's static-method/constructor dispatch requires an exact runtime type match — no numeric-literal coercion, no type-based overload resolution (breaks scilib `Series.from_values`/`Float32.new`/`Vec8f.splat`)

- **Date:** 2026-07-20
- **Status:** open (found triaging the `test/feature/scilib` cluster)
- **Area:** `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs`
  (`handle_constructor_methods`, `constructor_overload_score`,
  `constructor_value_matches_type`, `constructor_value_type_matches_name`),
  deployed seed at `bin/release/x86_64-unknown-linux-gnu/simple`. Same family
  as `doc/08_tracking/bug/host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17.md`
  (the deployed binary is confirmed a Rust-seed stopgap, not the true
  self-hosted binary — every invocation prints "this Rust-built Simple binary
  is a bootstrap seed only").

## Symptom

19 `test/feature/scilib` specs (`df_async_facade_spec`, `df_column_ops_spec`,
`df_concat_spec`, `df_construction_spec`, `df_filter_spec`,
`df_head_tail_spec`, `df_melt_spec`, `df_merge_spec`, `df_pivot_spec`,
`df_select_spec`, `df_sort_values_spec`, `df_symbol_intern_spec`,
`linalg_simd_spec`, `ndarray_broadcast_spec`, `ndarray_dtype_spec`,
`ndarray_reduction_spec`, `ndarray_simd_spec`, `ndarray_ufunc_spec`,
`simd_f32_spec`) fail under `bin/simple test <spec> --no-session-daemon`
with one of exactly 3 error strings, all "the method exists by name but a
static-dispatch call to it was rejected":

```
semantic: unknown static method from_values on class Series
semantic: unknown static method new on class Float32
semantic: unknown static method splat on class Vec8f
```

All three methods genuinely exist (`src/lib/nogc_sync_mut/df/mod.spl:64`,
`src/lib/nogc_async_mut/ndarray/mod.spl:9`,
`src/lib/nogc_sync_mut/simd.spl:162`) — this is not a rename/stale-API
situation. `bin/simple run <spec>` (interpreting the file directly, not via
the SSpec `test` command) reproduces the **identical** failures, so — unlike
the sibling bug
`enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md` —
this is not a test-path-vs-run-path divergence; it is a universal seed
interpreter limitation.

## Minimal repros

**(1) No numeric-literal coercion for typed constructor params.** A bare
float literal never satisfies an `f32`-typed static-method parameter, even
though the language has an `f32` literal suffix that does work:

```simple
use std.ndarray.*
fn main():
    val a = Float32.new(1.0f32)   # OK
    val b = Float32.new(2.0)      # FAILS: "unknown static method new on class Float32"
```

Crucially, this is not just a test-authoring gap: the exact same bare-literal
idiom is used throughout the **shipping library itself** —
`src/lib/nogc_async_mut/ndarray/mod.spl:286` (`flat_f32`'s dtype-mismatch
fallback: `return Float32.new(0.0)`) reproduces identically when exercised
directly:

```simple
use std.ndarray.*
fn main():
    val arr = array([Float64.new(1.0), Float64.new(2.0)])
    val v = arr.flat_f32(0)   # F64-dtype array -> hits `Float32.new(0.0)` fallback
```
```
error: semantic: unknown static method new on class Float32
```

So the library's own source is "broken" by the same standard the tests would
be judged by — this rules out "the tests should just add `f32` suffixes" as
the fix; the real defect is that the seed's static-dispatch path never
performs the numeric coercion a properly-typed call site is entitled to.

**(2) Same mechanism for a struct-typed array parameter**
(`Series.from_values(name: Symbol, values: [Float64]) -> Series` at
`src/lib/nogc_sync_mut/df/mod.spl:64`): calling it with `[Int64]` values
(as `df_construction_spec.spl:98-101` does, and as the library's own
`DataFrame.from_rows` does internally at `df/mod.spl:326`,
`Series.from_values(key, cols_i64[key.text])` where `cols_i64: {text:
[Int64]}`) fails the same way. Again the library's own internal call site
hits the identical defect, so this is not test-file drift.

**(3) Related, independently confirmed defect in the same subsystem:
duplicate same-name static methods do not overload-resolve by type at all —
the first-declared candidate always wins, silently, regardless of argument
type:**

```simple
struct Wrap:
    n: i64
    static fn make(values: [i64]) -> Wrap:
        Wrap(n: values.len())
    static fn make(values: [text]) -> Wrap:
        Wrap(n: values.len() * 100)
fn main():
    print "{Wrap.make([1, 2, 3]).n}"       # 3  (correct: first overload)
    print "{Wrap.make(["x", "y"]).n}"      # 2  (WRONG: silently ran first overload's
                                            #     body instead of erroring or picking
                                            #     the [text] overload; expected 200)
```
Reversing declaration order flips which formula "wins" for *both* calls —
confirming the second declaration is never reachable, not that the first is
semantically preferred. `handle_constructor_methods`'s `candidates`/
`constructor_overload_score` machinery (`objects.rs` ~line 158-181) reads as
though it supports multi-candidate type-based scoring, but in practice a
class registers only one `FunctionDef` per method name (dedup happens
upstream of this function, most likely at class/method-table construction),
so the scoring loop never actually sees more than one candidate for a
same-named pair. This means "add a second overload" is *not* a viable fix
for (2) above — it would compile but the added overload would be dead code.

## Root cause

`constructor_value_matches_type` / `constructor_value_type_matches_name`
(`objects.rs` lines 18-44) perform a **strict, non-coercing** runtime type
check per argument:
- `"f32" => matches!(self, Value::Float32(_))` (`value_impl.rs:582`) — a bare
  float literal evaluates to `Value::Float(f64)` by default (no expected-type
  context is threaded into literal evaluation at this call site), so it can
  never satisfy an `f32` parameter without an explicit `f32` suffix.
- `Value::Object { class, .. } => class == expected` — an `Int64` wrapper
  struct instance can never satisfy a `[Float64]`-typed array parameter,
  even where the call site (both in tests and in the library's own
  `from_rows`) clearly intends the numeric-tower classes to be
  interchangeable/coercible at this boundary.

If any single named static method has exactly one candidate and that
candidate's score comes back `None`, `handle_constructor_methods` falls
through past the enum-variant fallback straight to the misleading
`unknown static method {method} on class {class_name}` error (`objects.rs`
line 287) — misleading because the method exists; only the *type match*
failed. Separately, (3) suggests the class/method registration step
collapses same-named static methods to a single entry before this scoring
logic ever runs, which would explain why the scoring machinery is dead code
for the type-based-overload case.

Not verified against the pure-Simple self-hosted compiler/interpreter
(`src/compiler/`) or the JIT/native-compiled path — only the Rust seed
interpreter (the binary `bin/simple test`/`bin/simple run` currently
resolve to, per the seed-pinned deployment) was probed. It is plausible the
real self-hosted compiler performs proper static type inference before
constructor dispatch (implicit numeric widening at a typed call site) and
this defect is specific to the seed's untyped dynamic-dispatch fallback.

## Not fixed here

Per task scope: this is a `src/compiler_rust` interpreter defect that
requires a rebuild to fix and validate (`bin/simple build bootstrap`), which
this pass is scoped to avoid. The 19 affected scilib specs were left
unedited — do NOT "fix" them by adding `f32` suffixes or swapping
`Int64.new(...)` for `Float64.new(...)`; the shipping-library coherence
check above shows the current call sites are correct Simple and the seed is
the thing that's wrong. Classify all 19 specs as **ENV** (seed-pinned
deployment), pending redeploy of a true self-hosted `bin/release/<triple>/simple`.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/scilib/df_construction_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple run  test/feature/scilib/df_construction_spec.spl
bin/release/x86_64-unknown-linux-gnu/simple run  <repro (1)/(2)/(3) above>
```
All reproduce the described "unknown static method" errors / silent
first-wins overload behavior identically.

## Update 2026-07-20 — empirical: coercion fix built + validated, 0/19 under `test`

Implemented the numeric-widening fix in `constructor_overload_score` /
`constructor_value_matches_type` (int/float widen to a float param; strict match
keeps a +50 tie-break so exact overloads still win), rebuilt the seed, and ran all
19 scilib specs against it: **0/19 turned green.** Under `bin/simple test` (SSpec)
the error is `unknown static method new on class Float32` — which fires BEFORE any
overload scoring, i.e. the static method is never even resolved on the imported
numeric-tower class. So this is primarily a **static-method RESOLUTION gap on
imported classes under the SSpec test evaluator** (same family as
`enum_impl_static_fn_method_call_path_skips_impl_methods` and
`generic_class_static_method_unresolved_under_test_2026-07-20.md`), NOT the
overload-coercion gap. The coercion fix is correct for the `run` path (where the
library's own `Float32.new(2.0)` fails) but does not address the test-path
failures. Real fix = resolve imported class static methods under SSpec, THEN the
coercion gap becomes reachable. Source fix was NOT landed (fixes nothing measurable
on the test path; regression-risky on a hot path for zero suite benefit).
