# Bug: `m{}` math-DSL implicit multiplication mis-chains 3+ groups / unary-minus, and 1D-vector matmul rejected

- **Date:** 2026-07-20
- Status: OPEN (P2)
- Status re-verified 2026-08-17 **by execution** (see "Re-verification 2026-08-17"
  at the bottom) — root cause now isolated to two exact lines.
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  `test/feature/usage/math_render_spec.spl` — both "Status: Implemented")
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

## Re-verification 2026-08-17 — STILL FAILING, root cause isolated

Binary identity:
```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59537240 2026-08-17 12:58:51.339525019 +0000
```
(Still the Rust seed — `--version` prints the seed warning banner.)

Reduced repro (`m{}` bound to a `val` first — see note below), run as
`bin/simple test <repro>.spl --no-session-daemon`, exit 1:
```
  ✗ chains multiple groups          expected 4 to equal 8
  ✗ handles negative coefficient    expected -2 to equal -6
  ✗ handles subtraction vs negative expected -3 to equal -6
3 examples, 3 failures
Results: 3 total, 0 passed, 3 failed
```
All three reproduce the originally-filed numbers exactly.

**Secondary parse finding (new):** writing the assertion inline as
`expect m{ (a)(a)(a) } == 8` fails with `semantic: variable \`expect\` not
found` — an `m{...}` block directly in an `expect` argument position derails the
statement parse. Assigning to a `val` first is the workaround used above.

### Root cause — CONFIRMED, `src/compiler_rust/compiler/src/blocks/math/parser.rs`

Both remaining implicit-mul failures come from `is_implicit_mul` (lines
193-198), which whitelists only `Int | Float | Var | Group | Subscript` as an
acceptable left operand for an implicit product, and is consulted by the
`parse_multiplicative` loop at line 181:

- **`(a)(a)(a)` -> 4.** First iteration produces `left = Mul(Group, Group)`.
  On the next iteration the token is `LParen`, but `Mul(..)` is not in the
  whitelist, so `is_implicit_mul` returns false and the loop `break`s — the
  third group is dropped, not consumed. The chain is exactly 2 deep, matching
  the original hypothesis in "Root cause" above.
- **`-2x` -> -2 and `-x y` -> -3.** `parse_unary` (213-222) returns
  `Neg(Int(2))` / `Neg(Var(x))` before control returns to
  `parse_multiplicative`. `Neg(..)` is also not in the whitelist, so the
  following `Ident` is never folded in.

Minimal fix direction: extend `is_implicit_mul` to accept the results this same
level produces — `Mul`/`Div`/`Mod`/`MatMul` — and to recurse through `Neg`
(`Neg(inner) => is_implicit_mul(inner)`). That yields `-(2*x)` and `-(x)*y`,
both `-6`, and folds the full group chain.

`m{}` matmul 1D-promotion and the `Pow(Id(x), Id(?))` render defect were not
re-probed in this pass and remain as filed.

### Why not fixed in this pass

The `m{}` DSL has **no `.spl` implementation** — the only parser is the Rust
seed's `src/compiler_rust/compiler/src/blocks/math/parser.rs`. `src/compiler/15.blocks/**`
and `src/lib/common/science_math/**` carry only the `implicit_multiplication`
feature FLAG, no parsing. A fix therefore requires editing the Rust seed and
rebuilding + redeploying `bin/release/<triple>/simple`, which
`.claude/rules/bootstrap.md` warns against doing ad hoc in this shared tree.

## FIX APPLIED AND VERIFIED 2026-08-17 (20:1x) — implicit-mul half RESOLVED in tree

### Step 1 — re-reproduced on the newly redeployed seed

`bin/simple` md5 `669150b61f2f20401a6a895ae54e9fee`, 59550432 bytes, mtime
2026-08-17 20:10:45.

```
$ timeout 3000 nice -n 19 bin/simple test test/feature/usage/implicit_mul_spec.spl --no-session-daemon
    ✗ chains multiple groups             expected 4 to equal 8
    ✗ multiplies coefficient and matrix  expected [[2.0, 4.0], [6.0, 8.0]] to equal [[2, 4], [6, 8]]
    ✗ works in linear algebra            semantic: matmul requires 2D tensors
    ✗ handles negative coefficient       expected -2 to equal -6
    ✗ handles subtraction vs negative    expected -3 to equal -6
Results: 22 total, 17 passed, 5 failed          EXIT=1
$ timeout 3000 nice -n 19 bin/simple test test/feature/usage/math_render_spec.spl --no-session-daemon
    ✗ renders power right-assoc with unary  expected Pow(Id(x), Id(?)) to equal Pow(Id(x), Neg(Num(2)))
Results: 129 total, 128 passed, 1 failed        EXIT=1
```

Unchanged by the redeploy.

### Step 2 — the recorded fix, applied

`src/compiler_rust/compiler/src/blocks/math/parser.rs:193` `is_implicit_mul` now
also accepts the node kinds this level itself produces and recurses through
`Neg`:

```rust
match left {
    MathExpr::Int(_) | MathExpr::Float(_) | MathExpr::Var(_) | MathExpr::Group(_) | MathExpr::Subscript(_, _) => true,
    MathExpr::Mul(_, _) | MathExpr::Div(_, _) | MathExpr::Mod(_, _) | MathExpr::MatMul(_, _) => true,
    MathExpr::Neg(inner) => self.is_implicit_mul(inner),
    _ => false,
}
```

### Step 3 — rebuilt in an ISOLATED target dir and verified

```
$ cd src/compiler_rust && CARGO_TARGET_DIR=/mnt/data/cargo-target-verify-ccat \
    cargo build --release --bin simple      # Finished `release` profile
$ md5sum /mnt/data/cargo-target-verify-ccat/release/simple
fe852b91fde8886e9eed080b1487b22b   (59619744 bytes, 2026-08-17 20:17)

$ V=/mnt/data/cargo-target-verify-ccat/release/simple
$ $V test test/feature/usage/implicit_mul_spec.spl --no-session-daemon
    ✗ multiplies coefficient and matrix  expected [[2.0, 4.0], [6.0, 8.0]] to equal [[2, 4], [6, 8]]
    ✗ works in linear algebra            semantic: matmul requires 2D tensors
Results: 22 total, 20 passed, 2 failed          EXIT=1
$ $V test test/feature/usage/math_render_spec.spl --no-session-daemon
    ✗ renders power right-assoc with unary  expected Pow(Id(x), Id(?)) to equal Pow(Id(x), Neg(Num(2)))
Results: 129 total, 128 passed, 1 failed        EXIT=1
```

**All three implicit-multiplication failures are fixed** (`chains multiple
groups`, `handles negative coefficient`, `handles subtraction vs negative`;
17 -> 20 passed), with no new failure anywhere in either spec.

**Still OPEN (the two OTHER sub-defects this record tracks, untouched by this
fix):** (a) `m{}` matmul with a 1D array operand — `2A` now folds but produces a
float tensor and `A @ [1,2]` still errors `matmul requires 2D tensors`; (b) the
math-render `Pow(Id(x), Id(?))` placeholder for a unary-minus exponent. Both
need separate work in the same seed file family.

Fix is in tree but **NOT deployed**: the verification binary was deliberately
not copied over `bin/simple` (other lanes are using it), and this lane did not
commit.
Left OPEN with the evidence and the exact two-line fix location above.
