# Bug: `m{}` math-DSL implicit multiplication mis-chains 3+ groups / unary-minus, and 1D-vector matmul rejected

- **Date:** 2026-07-20
- **Status:** resolved — implicit-mul chain + 1D matmul fixed by ea30e1330fb (2026-08-31, ancestor of release/1.0.0); render unary-power defect fixed in `src/lib/common/math_repr.spl` (verified 2026-11-25, see end of file)
- **Area:** math-block (`m{...}`) DSL implicit-multiplication parsing/lowering
  and tensor `@` matmul operator, not isolated further in this pass, deployed
  seed at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`implicit_mul_spec.spl`, 4 failures:

```
✗ chains multiple groups
  val a = 2; m{ (a)(a)(a) }        --> expected 4 to equal 8   (only 2 of 3 groups multiplied: 2*2, third `(a)` dropped)

✗ works in linear algebra
  m{ 2(A @ x) + b }                --> semantic: matmul requires 2D tensors (x = [1,2] treated as 1D, not accepted)

✗ handles negative coefficient
  val x = 3; m{ -2x }              --> expected -2 to equal -6  (coefficient 2 dropped: result is just -x's sign applied to 2, not -2*3)

✗ handles subtraction vs negative
  val x = 3; val y = 2; m{ -x y }  --> expected -3 to equal -6  (only -x kept, *y dropped: -3, not (-3)*2=-6)
```

`math_render_spec.spl`, 1 failure — a **separate** rendering/AST bug in the
same DSL family:

```
✗ renders power right-assoc with unary
  expected Pow(Id(x), Id(?)) to equal Pow(Id(x), Neg(Num(2)))
```
The rendered AST shows a garbled `Id(?)` node in place of `Neg(Num(2))` for a
unary-minus operand inside a power expression — a distinct parse/render defect
from the arithmetic-chaining bugs above, but in the same `m{}` DSL area.

(Also observed but not filed as a separate defect: "multiplies coefficient and
matrix" reports `expected [[2, 4], [6, 8]] to equal [[2, 4], [6, 8]]` — the
printed values are identical; this looks like a nested-array/matrix deep-
equality matcher issue rather than a computation bug, and is folded into this
doc as a secondary observation rather than root-caused separately.)

## Root cause

Not isolated to specific source locations in this pass. The consistent
pattern across 3 of the 4 `implicit_mul_spec.spl` failures is that **only the
first two adjacent implicit-multiplication operands are combined**; any
further chained operand (a 3rd parenthesized group, or a trailing identifier
after a unary-minus'd coefficient×identifier pair) is silently dropped rather
than folded into the product. This suggests the implicit-multiplication
parser builds a left-associative chain only 2 levels deep, or the fold/reduce
step over a chain of 3+ implicit-mul operands terminates early.

## Fix direction (not applied — compiler-internals change, needs rebuild)

1. Trace the `m{}` block's implicit-multiplication parsing (adjacency-implies-`*`
   detection) for chains of 3+ operands (`(a)(a)(a)`, `-2x` as
   unary-neg(2)×x, `-x y` as unary-neg(x)×y) and confirm the fold covers the
   full operand list, not just the first pair.
2. Trace `A @ x` where `x` is a 1D array literal (`[1, 2]`) — confirm whether
   1D-vector-times-2D-matrix should auto-promote to a 2D column/row vector
   for `@` (matmul), matching common linear-algebra library conventions,
   before erroring with "matmul requires 2D tensors".
3. Trace the math-render AST builder for unary-minus operands inside power
   expressions (`Id(?)` placeholder instead of `Neg(Num(2))`).

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/implicit_mul_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/math_render_spec.spl --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.

## Verification 2026-11-25 (p2w3-ae lane, release/1.0.0 worktree) — both defect families fixed

**1. Implicit-mul chain + 1D matmul (the 4 `implicit_mul_spec.spl` failures):**
fixed by commit `ea30e1330fb` ("fix(math): implicit multiplication drops
factors; matmul rejects 1D operands (#134)", 2026-08-31), confirmed an ancestor
of the release/1.0.0 tip via `git merge-base --is-ancestor`. The commit removed
the shape-based `is_implicit_mul` guard in `parse_multiplicative` (the exact
"only the first two operands combine" mechanism this record suspected) and gave
`Tensor::matmul` NumPy-`@`-style 1D promotion. It landed with its own
regression spec, `test/01_unit/compiler/blocks/math_implicit_mul_precedence_spec.spl`.
Per the commit message, the 2 failures remaining in `implicit_mul_spec.spl`
after that fix are an unrelated int-vs-float design conflict between two
protected specs — not the chaining/matmul defects filed here.

**2. Render `Id(?)` for unary-minus exponent (`math_render_spec.spl` "renders
power right-assoc with unary"):** fixed in the pure-Simple renderer this spec
exercises (`std.math_repr` → `src/lib/common/math_repr.spl`).
`_power_debug` (:1064-1075) now handles a leading `-` at power level
(`Neg(...)` wrapping) and parses the exponent at power level ("right-associative
and accepts unary minus"), so `x^-2` yields `Pow(Id(x), Neg(Num(2)))`; the
`Id(?)` fallback in `_primary_debug` (:1062) is unreachable for a `-` token on
this path.

Runtime re-run of both specs in this lane was not possible: the pinned seed
binary at `bin/simple.exe` rejects the `@representation_boundary` decorator
added tree-wide by cfd89933699, so every `bin/simple.exe test` at release/1.0.0
HEAD fails in the test runner itself before reaching any spec. Verification is
by commit ancestry + code inspection; the mechanisms named above are decisive
for the filed symptoms.

**Verdict: STALE-CLOSED.**
