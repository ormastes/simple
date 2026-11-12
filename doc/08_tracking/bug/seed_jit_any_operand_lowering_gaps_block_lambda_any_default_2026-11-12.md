# Seed JIT: ANY-operand lowering gaps block the `ANY` default for unannotated lambda params (2026-11-12)

Status: OPEN. These gaps exist today for any `ANY` value (generic results,
placeholder lambdas). They become mainstream if an unannotated named lambda
parameter defaults to `ANY` instead of `I64`, so that change is NOT landed.

## Context

`\x: ...` with no expected type defaults its parameter to I64. That is wrong
for every non-integer argument (`["a", "b"].map(u)` with `val u = \x: x`
prints two garbage integers under the JIT today). Defaulting to `ANY` fixes
all of those (work branch `work/jit-lambda-any-default-wip-20261112`), but the
integer case then depends on every operator handling a tagged word.

## Measured: integer arguments, I64 default vs ANY default (seed JIT)

| Lambda | I64 default | ANY default |
|---|---|---|
| `\i: xs[i]` called with 2, `xs = [10, 20, 30]` | 30 | 0 |
| `\x: xs[x - 1] + xs[0]` called with 3 | 40 | 13 |
| `\i: ts[i] + "!"` called with 1 | b! | no output |
| `\x: Pt(x: x, y: x * 2)` called with 4 | 4,8 | 32,64 |
| `\x: x + 0.5` called with 2 | 2.5 (interpreter fallback) | 0.5 |
| `\x: -x` called with 2.5 | -2.5 (interpreter fallback) | `<value:0x...>` |

Unchanged and correct under both: `+ - * / %`, shifts, bit-and, comparisons
feeding `if`, typed calls, string interpolation, array literals, `while`,
dict index, `.len()`.

## Gaps (MIR lowering, `src/compiler_rust/compiler/src/mir/lower/`)

1. Array / text index with an `ANY` index: the tagged index goes straight to
   `rt_typed_words_i64_at`. Needs the tagged -> raw decode
   (`unbox_scalar_for_raw_slot`) on the index operand.
2. Struct construction storing an `ANY` value into a raw scalar field: no
   decode, the field holds the tagged word.
3. `ANY + <f64 literal>`: the mixed pair is not routed through the float lane.
4. Unary `-` on an `ANY` operand: raw negate of the word (right for a tagged
   int by coincidence, wrong for a float).

## Why it matters

Each gap is a silent wrong value for the common integer case that is right
today. The default must not flip until these four are fixed and a wider
operator sweep comes back clean.
