# StringBuilder is worse than naive `+` concat in the tree-walk interpreter, and gets worse than O(n^2) as n grows

- Status: OPEN
- Found: 2026-08-18
- Component: `src/lib/common/string_builder.spl` (`StringBuilder.push`/`.build`),
  interpreter class-method + array-push dispatch
  (`src/compiler_rust/compiler/src/interpreter_method/collections.rs`,
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`)

## Summary

Follow-up on `22faace491c` ("perf(text): adopt array-accumulator + join at 2
sites — to_upper_ascii, svmg disasm"), which adopted `common.string_builder.StringBuilder`
to replace `result = result + c` (documented O(n^2)) accumulation. That commit
was reverted (see below) after measuring both lanes across a range of n instead
of only the original 100-char corpus.

## Measurements (this repo, JIT-seed binary, `bin/simple run` on a standalone
bench comparing `upper_naive` (`+`-concat) vs `upper_sb` (`StringBuilder`) doing
identical ASCII-uppercase work over a synthetic corpus):

### JIT lane (`bin/simple run`, Cranelift):
| n | naive_us | sb_us | sb speedup |
|---|---|---|---|
| 100 | 63 | 68 | 0.93x (roughly break-even) |
| 1000 | 1134 | 506 | 2.2x |
| 5000 | 19339 | 3276 | 5.9x |
| 10000 | 73311 | 8362 | 8.8x |
| 30000 | 627377 | 54006 | 11.6x |

In the JIT lane, `StringBuilder` behaves exactly as intended: naive `+` grows
quadratically (627ms at n=30000), `StringBuilder` stays close to linear (54ms),
crossover is around n~100-300.

### Interpreter lane (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`):
| n | naive_us | sb_us | sb slowdown |
|---|---|---|---|
| 100 | 1160 | 1924 | 1.7x slower |
| 1000 | 12405 | 28715 | 2.3x slower |
| 5000 | 44477 | 344802 | 7.8x slower |
| 10000 | 92430 | 1208713 | 13.1x slower |
| 30000 | 314442 | 10823076 | **34.4x slower** |

In the interpreter, `StringBuilder` is not just constant-overhead-bound at
small n — it gets **relatively worse as n grows**, and its absolute growth rate
is *worse than the O(n^2) baseline it was meant to replace* (naive `+` interp
time grows ~27x from n=100->30000, i.e. sublinear-looking due to other fixed
costs dominating small n; `sb` time grows ~5627x over the same range). This
points to `StringBuilder.push` itself costing more than O(1) amortized per call
in the interpreter — plausibly the interpreter's array `.push()` (or the
class-instance field mutation/method-dispatch path backing it) is not
amortized-O(1) growth, making the "O(n) push + O(n) join" design actually
O(n^2)-or-worse in this lane, with a much higher constant than scalar text
concatenation.

## Root cause (not yet isolated to a single fix site)

Not confirmed by profiling — this needs follow-up. Suspects, ranked by the
measured shape (super-linear-in-n *slowdown ratio*, not just a constant
offset):
1. `[text].push()` in the interpreter reallocates/copies the whole backing
   array per call rather than amortized-doubling growth
   (`interpreter_method/collections.rs`).
2. Per-call class-method dispatch overhead on `StringBuilder.push` (instance
   field lookup/mutation) that itself scales with array size.
3. `.join("")` in `StringBuilder.build()` doing redundant work proportional to
   accumulated size on every intermediate step (unlikely given it's called
   once, but not ruled out).

## Decision: REVERTED

`22faace491c`'s two call sites (`text_ascii.to_upper_ascii`,
`svmg/assembler.disasm`) are reverted back to the original `result = result + x`
form in a follow-up commit, because:
- `bin/simple test` (the lane most of this codebase's specs and tooling run
  under, see `.claude/rules/testing.md`: "`bin/simple test` hard-defaults to
  the tree-walk interpreter") would see call sites get **dramatically slower**,
  not faster, from this "fix" — regressing real usage, not a benchmark
  artifact.
- The JIT-lane win is real but does not offset the interpreter-lane loss for
  library code whose caller engine is not controlled by the callee.
- `StringBuilder` itself needs a perf fix in the interpreter lane before it is
  safe to adopt as the general-purpose "avoid O(n^2) concat" remedy this
  codebase's other bug docs (C-MIG-0023, C-MIG-0035, base64_encode) point to.

## Follow-up required before StringBuilder is re-adopted anywhere

1. Profile/isolate why `StringBuilder.push` costs more than O(1) amortized per
   call in the interpreter (see suspects above).
2. Fix the interpreter-side array push (or class-method dispatch) cost.
3. Re-run this exact bench (`upper_naive` vs `upper_sb`) in the interpreter
   lane and confirm sub-quadratic scaling before re-adopting.
4. Only then re-apply the `to_upper_ascii`/`svmg/assembler.disasm` change,
   updating `test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl`'s
   perf_evidence corpus to a size (>=5000) where the win is real and
   documented, in both lanes.

## Related
- `22faace491c` (reverted commit)
- Bug C-MIG-0035 (original `to_upper_ascii` O(n^2) finding)
- `src/lib/common/string_builder.spl` — `RtStringBuilder` (runtime-backed,
  amortized O(1) push via a Rust-heap `String`) is a DIFFERENT type in the same
  file and was not exercised by this bench; it may not share this defect since
  it bypasses the Simple-level array entirely. Worth trying as the interpreter
  remedy in the follow-up above instead of fixing array-`StringBuilder`.
