# `s = s + x` on a scalar silently becomes `rt_array_extend_i64` and yields 0

- **Date:** 2026-08-23
- **Status:** OPEN — root cause proven down to the emitted instructions
- **Severity:** CRITICAL — silent wrong answer in the most ordinary code there is
- **Area:** `src/compiler/10.frontend/desugar/collection_desugar.spl` (Pattern B) +
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  (`lower_unresolved_array_merge`)
- **Regressed by:** the 2026-08-22 change that gave `merge` a MIR lowering
  (`mir_unresolved_method_call_merge_2026-08-22.md`)

## Symptom

Native only. The build reports rc=0, step 6/6, links, and the program computes
zeros.

```
var a: [i64] = [1, 2, 3]
var s = 0
for x in a: s = s + x
print(s)          # native prints 0, interpreter prints 6
```

## Isolation — it is NOT loops and NOT arrays

Measured on `74f2b254081`, every row built with `native-build` and EXECUTED,
against `simple run` on the same source:

| form | interp | native |
|---|---|---|
| `var s = 0; s = s + a[0]` | 1 | **0** |
| `var t = 0; t = t + e` (e a `val`) | 2 | **0** |
| `for x in a: s = s + x` | 6 | **0** |
| `while i < a.len(): t = t + a[i]` | 6 | **0** (loop terminated — `i = i + 1` DID land) |
| `for j in 0..3: u = u + 1` | 3 | 3 |
| `u = a[0] + a[1]` (no self-reference) | 3 | 3 |
| `var p = a[0]` | 1 | 1 |
| `var q = 0; q = q + 5` | 5 | 5 |

The discriminator is **`x = x + <non-literal>`**, nothing else. A literal
addend works; a self-reference-free sum works; the loop machinery works.

## Mechanism — read off the disassembly

`objdump` of `__simple_main` for `var s = 0; s = s + a[0]`:

```
call rt_array_get           ; a[0]
call rt_value_as_int_wide   ; -> 1
xor  %edi,%edi              ; arg0 = 0        <-- s, still its initial value
mov  %rax,%rsi              ; arg1 = 1
mov  $0xffffffffffffffff,%rdx
call rt_array_extend_i64    ; <-- an INTEGER ADD became an ARRAY EXTEND
...
xor  %edi,%edi
call rt_raw_i64_to_string   ; prints 0
```

`collection_desugar.spl` Pattern B rewrites `x = x + other` into
`x.merge(other)` at the **AST level, before type-checking**, so it has no type
oracle. Its `is_definite_scalar_addend` gate suppresses the rewrite only for
addend shapes that are *provably* scalar (int/float/bool/string/suffixed
literals, unary, binary). The file's own comment states the residual hole
plainly:

> It still fires for identifier / field-access / index / call-result addends
> (e.g. `a = a + d1`) because those shapes are genuinely ambiguous without type
> info … That ambiguity is a pre-existing, separate, out-of-scope concern.

`s = s + x` with `x` an identifier is exactly that shape. It is rewritten to
`s.merge(x)`, and `lower_unresolved_array_merge` lowers `merge` unconditionally
to `rt_array_extend_i64(dst, src, -1)`.

**What changed on 2026-08-22 is not the hole — it is the failure mode.** Before
`merge` had a MIR lowering, this shape died LOUDLY at build time with
`unresolved method call: merge`. Giving `merge` a lowering converted a loud
build failure into a silent wrong answer, which is strictly worse. The scalar
gate was written (2026-07-29) when the failure was still loud, and its
"out-of-scope" note was defensible under that assumption; it no longer is.

## Fix direction

The AST pass cannot be made type-aware. The type IS known at MIR lowering, so
the guard belongs in `lower_unresolved_array_merge`: emit
`rt_array_extend_i64` only when the receiver is genuinely a collection, and
otherwise lower the node as the scalar `x = x + y` it was desugared from.
Failing that, the desugar must record enough provenance for MIR to undo it.

Whatever the shape of the fix, it must NOT be "restore the loud build error" —
`a = a + d1` on real byte-array concatenation depends on the rewrite firing.

## Ship with

An engine-differential spec asserting the RUNTIME OUTPUT of every row of the
isolation table above, native vs interpreter, failing pre-fix.

## Fix as landed

`lower_unresolved_array_merge` now checks the receiver before emitting
`rt_array_extend_i64`. When the receiver's MIR type is an integer or float
width (and the local is not a known runtime array), the node is lowered as the
`x = x + y` it was desugared from: a `BinOp.Add` copied back into the receiver,
followed by the same writeback. The AST pass is unchanged, so every legitimate
Pattern-B rewrite on real collections still fires.

`local_hir_type_is_int` alone was NOT sufficient — measured: it returns false
for these accumulators, and a first attempt guarded only on it changed nothing
in the emitted binary. The MIR type is what is actually populated here. That
negative result is recorded because it is the obvious thing to try first.

Floats were folded into the same guard. `var f = 1.5; f = f + g` did not
silently produce a wrong number — it failed the BUILD with
`unsupported LLVM value conversion from double to ptr`, which is the same root
cause (a float receiver reaching the array-extend call) landing loudly instead
of silently. Same guard, same fix.

### Still broken, deliberately untouched: a `text` receiver

`var txt = "a"; val more = "bc"; txt = txt + more` prints `a` natively (should
be `abc`) — the same Pattern-B shape with a string receiver. An
`emit_raw_strcat` + copy-back arm was written and **measured still producing
`a`**, so it was removed: text is left on exactly the path it was already on
rather than swapped for a different wrong answer. This is a real open defect,
not a fixed one; the gate's compared set deliberately excludes the `str=` row
and says so, so its absence cannot be mistaken for text being correct.

### Verification

`src/app/_cg/f08v/main.spl`, built with `native-build` and EXECUTED, compared
against `simple run` on the same source. Post-fix native output:
`forin=6 while=6 aug=6 mergelen=4 last=5 augmergelen=3 float=3.75` — matching
the interpreter on every row, including the two that prove the collection path
did NOT regress (`c = c + b` and `d += b`).

### Gate

`sh scripts/check/check-scalar-accumulator-not-array-merge.shs` — builds the
fixture and diffs native output against the interpreter's. Engine-differential
on purpose: asserting native against a hardcoded expectation would pass the day
both engines break together. 0 lines compared, a missing compiler, or a
timed-out build are ERROR (exit 2), never a pass.
