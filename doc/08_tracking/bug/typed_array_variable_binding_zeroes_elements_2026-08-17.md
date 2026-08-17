# Binding a typed array variable to another variable zeroes its elements

**ID:** typed_array_variable_binding_zeroes_elements_2026-08-17
**Date:** 2026-08-17
**Severity:** P1 — silent wrong-answer bug. No diagnostic, correct length, wrong
contents. Found because it made X25519 compute the wrong shared secret.
**Status:** OPEN

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
