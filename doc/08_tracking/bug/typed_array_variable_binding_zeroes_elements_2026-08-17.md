# Binding a typed array variable to another variable zeroes its elements

**ID:** typed_array_variable_binding_zeroes_elements_2026-08-17
**Date:** 2026-08-17
**Severity:** P1 — silent wrong-answer bug. No diagnostic, correct length, wrong
contents. Found because it made X25519 compute the wrong shared secret.
**Status:** ROOT-CAUSED and FIXED 2026-08-17 in `rt_array_copy`
(`src/compiler_rust/runtime/src/value/collections.rs`), commit `a4cc6f61dfb`.

## Root cause — it was never "zeroing", it was a divide by eight

The title understates it. Elements were not zeroed; they were **divided by 8**.
`5 >> 3 == 0`, which is why small fixtures looked like zeroing and the real
mechanism stayed hidden. The discriminating measurement:

```
u64-small orig 5                    copy 0                   want 5
u64-big   orig 1234567890123456789  copy 154320986265432098  want 1234567890123456789
```

`1234567890123456789 / 8 == 154320986265432098` exactly. That is an untagging
`>> 3`, not an uninitialised buffer.

Mechanism: `[u64]` arrays use a **packed** heap layout (`gc_flags::U64_PACKED`)
whose `data` slots hold RAW 64-bit words rather than tagged `RuntimeValue`s.
`rt_array_copy` walked the source with the generic `as_slice()` +
`rt_array_push` loop, which is wrong twice over — it reinterprets each raw word
as a tagged value, and it produces an **unpacked** result whose reader then
untags whatever it finds. Length was copied correctly, which is exactly why a
`.length()` check could never have caught it.

`val b = a` on any array-typed binding lowers to `rt_array_copy`
(`compiler/src/mir/lower/lowering_stmt.rs:209-230`), so this reached ordinary
user code. That lowering already excluded `TypeId::U8` with a comment saying
byte-packed arrays are "a separate heap layout that rt_array_copy's
rt_array_push-based copy loop does not understand" — the identical hazard, one
element type away, documented and worked around rather than fixed.

## Scope — measured, not assumed

| element type | pre-fix result |
|---|---|
| `[u64]` | **BROKEN** — every element divided by 8 |
| `[i64]`, `[f64]`, `[u8]`, `[u32]`, `[u16]`, `[text]`, `[bool]` | correct |

| engine | pre-fix result |
|---|---|
| cranelift JIT (`bin/simple run`) | **BROKEN** |
| tree-walk interpreter (`SIMPLE_EXECUTION_MODE=interpreter`, and `bin/simple test`) | correct |

This is the same engine-divergence shape as the f32 struct-field defect fixed
the same night (`ac438753ebb`): a width/representation disagreement between the
store side and the load side, wrong only under the JIT.

## Fix

`rt_array_copy` now reproduces the source layout instead of flattening it: a
packed-u64 source allocates a packed-u64 result and `memcpy`s the raw words; a
byte-packed source does the same with bytes. The byte-packed arm also closes the
`[u8]` gap the codegen guard documents, so that exclusion is now unnecessary —
it is deliberately left in place to keep the change's blast radius bounded, and
removing it is a separate, testable follow-up.

## Unrelated defect noticed while sweeping the matrix

`[i8]` reads back wrong **before** any copy: `[5i8, 6i8]` gives `orig 43` for
element 0 under the JIT. The copy is faithful (43 -> 43), so this is NOT the
same defect and is not addressed here. Filed separately as
`doc/08_tracking/bug/i8_array_literal_reads_back_wrong_value_2026-08-17.md`.

## Summary

Binding an existing `[u64]` variable to another variable produces an array of
the **correct length** whose elements are **all zero**. Only a binding whose
right-hand side is a direct function call copies the contents.

There is no error, no warning, and `.length()` is right — so the value looks
healthy at every cheap check.

## Reproduction

`bin/simple run` (tree-walk interpreter path), deployed seed 2026-08-16:

```
fn mklist() -> [u64]:
    [5u64, 6u64]

fn main():
    val a = mklist()
    val c = a
    var d = a
    val g: [u64] = [3u64, 4u64]
    val h = g
    print("val<-call {a[0]}")     # 5  correct
    print("val<-val  {c[0]}")     # 0  WRONG, expected 5
    print("var<-val  {d[0]}")     # 0  WRONG, expected 5
    print("val<-literal {h[0]}")  # 0  WRONG, expected 3
    print("len {a.length()} {c.length()}")   # 2 2 — length survives
```

Measured output:

```
1 val<-call     a0=5 expect 5
2 var<-call     b0=5 expect 5
3 val<-val      c0=0 expect 5
4 var<-val      d0=0 expect 5
5 val<-var      e0=0 expect 5
6 var<-var      f0=0 expect 5
7 val<-literal  h0=0 expect 3
8 len a=2 c=2 e=2
```

So the rule is: **RHS is a call → contents copied. RHS is a variable (or a
literal bound to a name and then rebound) → contents zeroed, length kept.**

A swap written the ordinary way is therefore silently destructive:

```
val t = a
a = b
b = t      # b is now all zeros, not the old a
```

measured `a0=9 b0=0`, expected `a0=9 b0=1`.

## Impact found so far

`src/lib/nogc_async_mut_noalloc/tls/x25519.spl` initialised the Montgomery
ladder with `var x_3 = u`. `x_3` became all-zero — the point at infinity — so
the ladder collapsed and X25519 returned a wrong shared secret for every input,
while still returning 32 plausible-looking bytes. Both RFC 7748 KATs failed and
`x25519(a, pub_b) != x25519(b, pub_a)`. Worked around there by re-deriving
`x_3` through a call, with a comment pointing at this record.

This construct is idiomatic, so other typed-array code is likely affected. Any
`[u64]`/`[u8]` value passed around by rebinding rather than by call result
should be treated as suspect until this is fixed.

## Runner divergence — the spec does NOT bite, the probe does

Measured 2026-08-17, and it must not be glossed over:

| runner | engine | result |
|---|---|---|
| `bin/simple run` | JIT, falls back to interpreter | **5 of 7 checks FAIL** — defect reproduces |
| `bin/simple test` | tree-walk interpreter | `6 total, 6 passed, 0 failed` — defect absent |

So `test/01_unit/compiler/typed_array_variable_binding_spec.spl` is **green today
and therefore proves nothing**; it is retained as the assertion that should hold
and will catch the defect if it spreads to the spec engine. The biting evidence
is the run-path mirror
`test/01_unit/compiler/probe_typed_array_variable_binding.spl`:

```
PASS val<-call: got 5
FAIL val<-val: got 0 want 5
FAIL var<-val: got 0 want 5
FAIL var<-var: got 0 want 5
FAIL val<-literal: got 0 want 3
PASS length-preserved: got 2
FAIL swap-carries-value: got 0 want 5
TYPED_ARRAY_BINDING PROBE: 5 FAILED
```

Two things to note. The `length-preserved` check PASSES in the failing run —
it is exactly the assertion that would miss this defect, which is why the
element checks exist. And the probe **exits 0 while failing**, so the verdict
line is the authoritative signal, never the exit status.

This is the documented `run`-vs-`test` divergence class
(`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`): the two
runners are different engines, and a green spec does not cover the run path.

## Verification remaining

- Determine whether this reproduces on a freshly built self-hosted binary or is
  specific to the deployed seed (2026-08-16). The evidence above is from the
  seed, which is the engine `bin/simple test` also uses.
- Establish the element-type scope: measured on `[u64]`. `[u8]`, `[i64]` and
  generic `list` are untested.
- Establish whether the JIT path diverges from the interpreter path here.

## Regression spec

`test/01_unit/compiler/typed_array_variable_binding_spec.spl` (and its
`test/unit/` mirror) pins the copy semantics directly.
