# Seed JIT: ANY-operand lowering gaps block the `ANY` default for unannotated lambda params (2026-11-12)

Status: FIXED on `work/jit-any-operand-gaps-20261112`. The four gaps below,
three more found by a wider sweep, and the lambda-parameter type recovery are
fixed; the default is flipped in the same stack.

| Commit | What |
|---|---|
| `f8c28afd9a5` | array/text index, struct field init, `ANY` + numeric, unary minus |
| `003762ac439` | range bound (`for i in 0..v`), field assignment (`p.x = v`), numeric cast (`v as f64`) |
| `3256c1b3ece` | a lambda parameter's own type is used inside its body (`\i: xs[i]`) |
| `47422985fec` | closure-holding local gets a pointer-sized slot |
| `b9f9277fe0e` | unannotated lambda params default to `ANY`; declared `ANY` closure boundaries admitted |
| `c21de391b02` | mutex lock FFI result declared `i64?` (needed once the boundary is admitted) |

After the stack: a 35-shape `any`-parameter operator sweep has no mismatch,
and a 30-shape integer lambda sweep (each case isolated) matches the old I64
default with no regression. Tests: `mir::lower::tests::any_operand_gaps`.

Known remaining limit: `v as <integer type>` with `v: any` holding a FLOAT is
decoded as a tagged integer.

Original report follows.

These gaps existed for any `ANY` value (generic results, placeholder
lambdas). They become mainstream if an unannotated named lambda parameter
defaults to `ANY` instead of `I64`.

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
