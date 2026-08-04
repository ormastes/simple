# A `T?` value bound to a `bool` parameter is neither presence-coerced nor rejected — it arrives as the raw payload (2026-08-04)

**Status:** OPEN
**Found:** 2026-08-04
**Related — SAME root cause, found independently by parallel lanes the same day.
Fix once, close all four:**
- `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04.md`
  (unit tier — 28 specs in `test/01_unit/std/`; also records the JIT re-tagging
  half and a prior session that papered over two specs by editing the test)
- `exists_check_contract_reddens_46_app_branch_coverage_specs_2026-08-04.md`
  (app tier — 46 specs / 138 examples)
- `exists_check_on_optional_i64_returns_payload_2026-08-01.md` (earlier lane)

**This file is the SYSTEM-tier census** (`test/03_system/**`, `test/system/**`):
the corpus-wide count and the exact per-directory attribution below are the part
the sibling reports do not have.
**Class:** silent wrong answer + missing type check. **The single largest
failure cluster in the whole system-test corpus.** `verify(<expr>.?)` appears
**2,174 times across 1,676 spec files** — 1,087 occurrences in 838 files of
`test/03_system/`, and the identical 1,087/838 in the duplicate legacy tree
`test/system/`:

| directory (per tree) | spec files carrying the idiom |
|----------------------|-------------------------------|
| `infrastructure/batch` (`test/system/batch`) | 500 |
| `core/error_path` | 100 |
| `stdlib` (`stdlib_comprehensive_*`) | 50 |
| `core/edge_case` | 50 |
| `compiler/runtime_comprehensive` | 50 |
| `compiler/comprehensive` | 50 |
| everything else | 38 |

Measured impact where the tier was actually run:
`test/03_system/core` — **249 of 249** failing examples are this defect (all 150
failing files carry the idiom; 100 files x 1 + 1 x 2 + 49 x 3 = 249, an exact
match). `test/03_system/stdlib` — 51 of 63. `test/03_system/compiler` — 50 of
the `comprehensive/*` failures.

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple` (on this tree
that is the **Rust seed** — `bin/simple --version` prints the seed banner).
`bin/simple test` executes specs on the interpreter.

## Symptom

Minimal repro — a `bool`-declared parameter receiving a `T?`:

```
fn takes_bool(b: bool) -> text:
    if b:
        return "TRUE"
    return "FALSE"

fn main():
    val o = Some(99)
    print "o.?          = {o.?}"           # 99      (correct: `.?` returns T?)
    print "takes_bool(o.?) = {takes_bool(o.?)}"
```

Actual (interpreter): `takes_bool` receives the **raw payload `99`**, not
`true`. No diagnostic is emitted at any stage — not at parse, not at
resolve/semantics, not at the call site.

Where this bites, verbatim from the failing specs (each declares its own
`fn verify(condition: bool): expect(condition).to_equal(true)`):

| spec | expression | reported failure |
|------|-----------|------------------|
| `core/edge_case/edge_case_11_system_spec.spl:41` | `verify(opt2.?)` where `opt2 = Some(42)` | `expected 42 to equal true` |
| `core/edge_case/edge_case_11_system_spec.spl:79` | `verify(nested.?)` where `nested = Some(Some(Some(10)))` | `expected Option::Some(10) to equal true` |
| `core/edge_case/edge_case_11_system_spec.spl:157` | `verify(d.get("a").?)` | `expected 1 to equal true` |
| `core/error_path/error_path_100_system_spec.spl:182` | `verify(opt.?)` where `opt = Some(nil)` | `expected nil to equal true` |
| `stdlib/stdlib_comprehensive_1_system_spec.spl:96` | `verify(result.?)` | `expected 99 to equal true` |

Note the control case in the same block passes:
`verify(not d.get("c").?)` is fine, because `not` forces a real `bool`.

## Root cause (what is PROVEN)

1. **`.?` is behaving to contract, and must not change.**
   `doc/07_guide/quick_reference/syntax_quick_reference.md:505` — "Existence
   Check (`.?`) — Returns `T?`". The pure-Simple lowering
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2895-2902`) carries
   an explicit comment forbidding the collapse to a bare `rt_is_some` bool,
   citing the native-smoke-matrix "(14) Option/nil check (x.?)" regression where
   `if val v = x.?: return v` returned `1` instead of the payload. So the fix is
   NOT "make `.?` return bool".

2. **The gap is at argument binding.** The interpreter's parameter coercion hook
   is `coerce_param` in
   `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs:84`
   (a second copy at `:394`). It already performs two coercions:
   unsigned-width masking for `u8..u64` params (`:86-111`), and
   `Some(x) -> x` unwrapping when the target param is a concrete non-Optional
   type (`:112-131`). There is **no arm for a `bool`-declared parameter**, so a
   `T?` (or its already-unwrapped payload) falls through
   `copy_value_type_parameter` at `:132` untouched.

3. **The type checker does not reject it either.** No diagnostic is produced for
   `takes_bool(o.?)` at any stage, so the mismatch is invisible until an
   assertion downstream compares the payload against `true`. Silently accepting
   AND silently mis-binding is the actual defect: one of the two behaviours has
   to be chosen.

4. **The documented truthiness contract says the coercion should be
   presence-based.** `syntax_quick_reference.md:620` and `:626` define
   `opt.is_none()` as `not opt.?` and `list.is_empty()` as `not list.?`. Both
   identities only hold if a `T?` in a boolean position collapses to
   present/absent. Under that rule every failing example above is asserting
   something true.

## Blast radius beyond the spec tier

This is not test-only. Any product call `f(b: bool)` fed a `T?` — e.g. from a
`-> T?` helper or a `.?` — currently passes the payload. Under the interpreter
a nil payload happens to read falsy, so the wrong value is often masked; under
the JIT it does not (see the sibling bug
`jit_if_nil_takes_true_branch_2026-08-04.md`, where a nil bound to a `bool`
parameter takes the TRUE branch). The two bugs compound: the payload leaks in,
and then the branch test on it is also wrong.

## Why not fixed now

The fix site is inside the **Rust seed** (`arg_binding.rs`, two `coerce_param`
copies), which this repo's standing rule reserves for bootstrap and which needs
a `--full-bootstrap` cargo rebuild to take effect — a rebuild that would swap
the shared `bin/simple` out from under the parallel sessions live in this tree.

More importantly the change is a **language-semantics decision, not a local
patch**: adding "presence-coerce into a `bool` param" also has to answer what
happens for the other non-bool values at the same binding site (`0`, `""`, empty
collections, a plain `Int`), or it will silently accept `takes_bool(42)` as
`true` and convert today's loud wrong answer into a permanent quiet one. The
same table then has to be applied identically in the pure-Simple interpreter,
the Cranelift JIT and native codegen, or it just moves the divergence.

Recommended shape of the real fix, in order of preference:
1. Emit a semantic error when a non-`bool` static type is bound to a `bool`
   parameter, **except** for `T?`, which presence-coerces. This keeps
   `verify(x.?)` working (as the docs promise) and makes `takes_bool(42)` the
   compile error it should always have been.
2. Apply it in ONE shared place per engine, alongside the existing
   `Some(x) -> x` unwrap, so the three engines cannot drift.
