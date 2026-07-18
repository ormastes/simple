# Bug: `.to_int()` on `.split()`-derived text + `??` fallback both return garbage (Rust seed interpreter)

- **Date:** 2026-07-17
- **Status:** ROOT-CAUSED + FIXED 2026-07-18 (lane P6)
- **Area:** `src/compiler_rust` **native JIT/codegen path** (HIR lowering), NOT the
  tree-walking interpreter. `bin/simple run`'s default execution mode is
  `ExecutionMode::Jit` (JIT compilation with interpreter fallback); this bug is
  in the JIT-compiled path. Running the same repro with
  `SIMPLE_EXECUTION_MODE=interpret` (forcing the pure AST tree-walking
  interpreter) always gave the correct value, which is what led to the
  root cause below.

## Symptom

`text.to_int()` called on a string produced by `.split(":")` indexing (e.g.
`parts[1]`) returns `nil` even for a genuinely numeric string like `"42"` --
confirmed via `match ... case nil / case Some(v)`. Separately, `?? 0` applied
to that same `Option<i64>` (whether stored in a `val` first or chained
directly) does **not** produce the literal fallback `0`; it produces an
unrelated, non-deterministic large integer (looks like uninitialized memory /
a reinterpreted pointer), and even prints with the wrong type (`0` shows as a
float `0.00000000000000000` in one variant).

## Minimal repro

```simple
fn main():
    val parts = "hello:42:world".split(":")
    print "parts[1]={parts[1]}"          # prints "42" correctly

    val n = parts[1].to_int() ?? 0
    print "n={n}"                        # BUG: garbage int, not 42 and not 0

    val n2 = parts[1].to_int()
    match n2:
        case nil:
            print "n2 is nil"            # BUG: takes this branch for "42"
        case Some(v):
            print "n2 = {v}"
```

Actual output (Rust seed, `src/compiler_rust/target/release/simple run <file>`):
```
parts[1]=42
n=3102443233537
n2 is nil
```
(The garbage integer differs between runs -- e.g. a second run produced
`5161544509281` for the equivalent `?? 0` expression.)

Expected: `parts[1].to_int()` should be `Some(42)`, and if it were ever
legitimately `nil`, `?? 0` should yield exactly `0` (as `i64`).

## Workaround used

`src/app/stats/doc_coverage_dynamic.spl`'s `print_missing` needed to compare
grep-derived `file:line` matches without going through `.to_int()`/`??` at
all: it keeps line numbers as strings (`parts[1]` from `.split(":")`, no
numeric parsing) and matches them via a plain `text.contains(...)` substring
check against a second grep pass shaped into the same `"path-N-..."` format.
No numeric parsing needed, so the interpreter defect above never triggers.

## Root cause

The `??` framing in the title/repro is a **red herring**. `to_int()` is
implemented everywhere (interpreter and native runtime) to return a raw `i64`
directly (`0` on parse failure) -- never an `Option<i64>` -- so `?? default`
on it is close to a no-op once `to_int()` itself is correct. The actual
bug reproduces identically with the `??` removed entirely
(`val n = parts[1].to_int()` alone already showed the garbage), and even for
a bare string **literal** with no `.split()`/array involved at all
(`"42".to_int()`), which is what led to finding the true root cause below.

**Mechanism:** `lower_builtin_method_call()` in
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` has a `result_ty`
lookup table that gives a builtin string method a concrete, correctly-typed
HIR node (`HirExprKind::MethodCall { dispatch: DispatchMode::Static, ty }`).
Any method **not** listed in that table instead falls through to the generic
"user-defined method" path in `lower_method_call()`
(`dispatch: DispatchMode::Dynamic`, return type from a cross-type
`.<method>` suffix search in `lookup_method_return_type()`). For methods
reached only through that fallback, the compiled call resolves to an
**identity pass-through of the receiver** instead of actually invoking the
runtime function -- the receiver's own (string) pointer flows out typed as
whatever the fallback guessed (here `I64`, because some other type in the
program also has a method literally named `to_int`/`to_i64`, and the
suffix/bare-name resolution used by the fallback path picks that unrelated
numeric-conversion identity semantics instead of `rt_string_to_int`).
Printing/using that raw string pointer as a native `i64` then misdecodes the
NaN-boxed tag bits of the pointer bit pattern: a tiny near-zero float for a
statically-allocated literal string's pointer (`TAG_FLOAT`-colliding low
bits), or an ASLR-varying huge integer for a heap-allocated `.split()`
element's `RuntimeString` pointer (`TAG_HEAP`-colliding low bits, confirmed
by decoding several repeated garbage values: all `≡ 1 (mod 8)` = `TAG_HEAP`,
with matching low-order hex digits across runs and only the ASLR-randomized
high bits differing).

Two entries were missing from that table, both required to fully fix the
bug-doc repro:
1. **`"to_int" | "to_i64"`** -- missing entirely, so `.to_int()` on ANY
   String-typed receiver (even a bare literal) fell through to the broken
   generic-dispatch fallback.
2. **`"split"`** -- also missing, so `"...".split(sep)`'s own return type was
   never registered as `Array<String>`; it silently degraded through the same
   generic-dispatch fallback to an effectively type-erased array. Fixing (1)
   alone therefore still left `parts[1].to_int()` broken, because `parts[1]`'s
   element type was not `String` at the `.to_int()` call site (verified
   empirically: `.replace()`/`.len()` on a split element worked before either
   fix -- those methods happen to resolve unambiguously through the
   generic-dispatch fallback by bare name -- while `.to_int()` did not, until
   `split` was also given a concrete `Array<String>` return type).

This is the **same bug class** already fixed twice before in this exact table
for `"length"` (alias of `"len"`) and `"bytes"` -- see the inline comments
immediately above the new entries in `hir/lower/expr/mod.rs` and
`jit_string_length_var_control_flow_wrong_value_2026-07-17.md` /
`seed_interp_bytes_u8_relational_boxtag_shift_2026-07-17.md`. Any builtin
string/array method not listed in this table (or its `is_any` sibling table a
few dozen lines below) is at risk of the same silent-garbage failure mode;
`.to_upper()`/`.to_lower()` were observed to *also* be missing and *also*
broken (silent no-op pass-through) during this investigation, but are left
unfixed here as out of scope for this specific bug (filed separately if not
already tracked).

## Fix

`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`, in
`lower_builtin_method_call()`'s `is_string` `result_ty` match: added
`"to_int" | "to_i64" => Some(TypeId::I64)` and
`"split" => Some(self.module.types.register(HirType::Array { element: TypeId::STRING, size: None }))`,
mirroring the existing `"bytes"` entry's pattern.

Not fixed / explicitly out of scope: the `case nil` / `case Some(v)` match
arms in the original repro's `n2` variable are a **separate, pre-existing**
pattern-matching quirk (matching a raw non-Option `i64` against `Some(v)`
binds `v` to the raw value rather than failing to match) -- unrelated to the
garbage-value bug fixed here, since `to_int()` never actually returns an
`Option`. Not investigated further per scope.

## Verification

Repro reduced to (see `test/01_unit/bugs/interp_to_int_split_result_nil_coalesce_garbage_spec.spl`):
```simple
fn main():
    val parts = "hello:42:world".split(":")
    val n = parts[1].to_int() ?? 0
    print "n={n}"
```

Before fix (freshly rebuilt `simple-driver`, default `SIMPLE_EXECUTION_MODE`
i.e. JIT mode, matching what `bin/simple run` uses in production):
```
n=5583323588929      # run 1
n=3642635904385      # run 2 (non-deterministic; all ≡ 1 mod 8 = TAG_HEAP)
```
Even the coalesce-free, array-free literal case was broken:
```
val n = "42".to_int()
# printed: 0.00000000000000000   (TAG_FLOAT misdecode of the literal's pointer)
```

After fix (same binary, same execution mode, rebuilt from the two `mod.rs`
table entries above):
```
n=42                 # every run, deterministic
```
`SIMPLE_EXECUTION_MODE=interpret` (tree-walking interpreter) gave the correct
`n=42` both before and after the fix -- confirming the interpreter itself was
never the buggy component; only the JIT/native path was.

Regression coverage added at
`test/01_unit/bugs/interp_to_int_split_result_nil_coalesce_garbage_spec.spl`
(literal `to_int()`, literal `to_int() ?? 0`, split-derived `to_int()`,
split-derived `to_int() ?? 0`, and a non-numeric-input sanity check that
`to_int()` still returns `0` and not garbage). Also smoke-tested for
regressions on neighboring string/array methods after the fix: `.len()`,
`.replace()`, `.bytes()`, iteration (`for p in parts`), and array indexing on
`.split()` results all still behave correctly.
