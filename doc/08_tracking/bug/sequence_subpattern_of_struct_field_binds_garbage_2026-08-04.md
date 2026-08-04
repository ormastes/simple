# Array/tuple sub-pattern of a STRUCT FIELD binds garbage on the JIT

**Status:** OPEN (JIT binder). Condition side is correct; only the element
binders are wrong.
**Found:** 2026-08-04, while fixing top-level struct-pattern refutability.
**Engines:** JIT only. The tree-walk interpreter answers every row correctly.

## Symptom

```
struct Holder:
    xs: [i64]
    t: (i64, i64)

fn f(h: Holder) -> i64:
    match h:
        case Holder([a, b], (c, d)):
            print("a={a} b={b} c={c} d={d}")
            a + b + c + d
        case _: -1

fn main() -> i64:
    print("f {f(Holder(xs: [6, 8], t: (2, 5)))}")
    0
```

```
a=<value:0x6> b=1 c=2 d=5
f 64
```

Correct answer is `6 + 8 + 2 + 5 = 21`. The TUPLE field binds correctly
(`c=2 d=5`); the ARRAY field does not — `a` comes back as an undecoded tagged
value whose payload is the right number, and `b` is `1` instead of `8`.

## The arm selection is RIGHT — only the binders are wrong

This is not the irrefutable-matcher family. With
`test/fixtures/compiler/top_level_struct_subpattern_matrix.spl`:

| row | subject | arm taken | answer | correct |
|---|---|---|---|---|
| `d2_seq_hit`  | `xs=[0,7]` | arm 1 (literal `0` matched) | 56 | 14 |
| `d2_seq_miss` | `xs=[3,4]` | arm 2 (literal `0` rejected) | 156 | 114 |
| `d2_seq_len1` | `xs=[6]`   | arm 1 (`[a]`, length 1)     | 56 | 13 |
| `d2_seq_len2` | `xs=[6,8]` | arm 2 (`[a,b]`, length 2)   | 164 | 121 |

Every arm is selected correctly, including the element-literal test and the
array-length discriminator — so `struct_fields_condition` /
`sequence_condition` over a `FieldAccess` slot work. Only the values bound are
wrong.

## What identifies the broken half

Hoisting the field into a local at the `.spl` level makes it correct:

```
fn hoisted(h: Holder) -> i64:
    val ys = h.xs
    match ys:
        case [a, b]: a + b      # prints a=6 b=8, answers 14
        case _: -1
```

So the element walk (`sequence_element_slots` -> `Index { receiver: slot }`) is
right for a slot that is a plain `Local`, and wrong for a slot that is a
`FieldAccess`. The same walk over an ENUM PAYLOAD slot is also correct
(`case Items([a, b])` in `nested_payload_subpattern_depth_matrix.spl` passes),
which narrows it further: it is specific to the `FieldAccess` receiver.

## What was tried and did NOT work

Materialising the field into a compiler-generated temp local inside
`bind_struct_fields` — emitting `Let tmp = FieldAccess(subject, i)` and then
binding elements off `Local(tmp)` — mirrors the working `.spl` hoist exactly and
changed **nothing**: all four rows answered the same 56/156/56/164. So the
difference is not simply "receiver is a temp local vs a field load"; something
about the HIR-level `Let` of a sequence-typed field, or the ANY-typed `Index`
that follows it, is lost further down (MIR or codegen). That code was NOT kept —
an ineffective workaround is worse than none.

Next step should be MIR-level, not HIR-level: dump the MIR for `f` above and for
`hoisted` and diff the element reads.

## Coverage

`test/fixtures/compiler/top_level_struct_subpattern_matrix.spl` runs these four
rows on every invocation and reports them under `OPENCOUNT`, separate from the
`BADCOUNT` gate, so they stay measured and visible rather than deleted. When
this is fixed, move them into the `bad` tally.
