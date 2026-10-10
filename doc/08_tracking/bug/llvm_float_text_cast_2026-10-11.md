# float(text) reached LLVM as a pointer-to-number cast

Status: source repair candidate; execution and cross-target qualification pending.

The exhaustive module matrix rejected `type_check_eval_comparison_predicate`
in `src/compiler/10.frontend/core/type_checker.spl` with an unsupported LLVM
conversion from `ptr` to `double`. Its source performs `float(compare_str)`.
`float`/`f64` accepts text in the language builtin implementation; treating
that text pointer's address as a number would silently change its meaning.

Pure-Simple `MirLowering.lower_cast_expr` previously emitted a numeric MIR
Cast for all non-enum conversions. The repair recognizes a proven text local,
normalizes its tagged-string ABI once, calls the canonical
`rt_string_to_float` parser, and checks nil tag `3`. Success unboxes the
floating-point value through `rt_value_as_float`; failure calls `rt_panic`
with its complete pointer/length ABI and terminates as unreachable. A valid
zero is distinct from parse failure. Numeric casts keep their existing path.
Known pointer/aggregate sources get a fatal MIR semantic diagnostic, not
pointer-address arithmetic or unchecked LLVM conversion.

The LLVM unsupported-cast checks remain intact. Draft PR 2838 changes MIR
Bitcast lowering in `aggregate_intrinsics.spl`; it does not repair this
semantic text conversion. PR 2840 contains that patch alongside unrelated GPU
runtime changes. Neither draft was blindly applied.

## Regression and baseline evidence

- `test/fixtures/compiler/float_text_cast.spl`: decimal/exponent, zero,
  explicit `f64`, and unchanged numeric conversion checks.
- `test/fixtures/compiler/float_text_cast_invalid.spl`: trailing junk must
  panic before its invalid-input acceptance marker can execute.
- `test/fixtures/compiler/float_pointer_cast_invalid.spl`: class address
  conversion must fail semantically before object emission.
- `test/01_unit/compiler/mir/float_text_cast_mir_spec.spl`: four authored
  real-lowering cases; no execution PASS is claimed yet.

The positive fixture reproduced `unsupported LLVM value conversion from ptr
to double` with the existing pure-Simple producer SHA-256
`67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`,
exit 134, without an object. Its log/cache are retained under
`build/native_probe/llvm-cast-roots/float-before*`. The source base is
`1f3316d7dbc0db6f4cf8cf83d2a15dff7167e02f`.

The root's coordinated compiler build must include this change before the
native positive/negative fixtures and original module are rechecked. ARM
objects must be EM183 and RISC-V objects EM243 using LLVM18 and explicit
source/entry/target selection. No full compiler build was started here and no
RISC-V execution is claimed.

The canonical parser's whitespace/hexadecimal spelling difference from the
legacy seed builtin is explicitly tracked in
`float_text_cast_parser_spelling_divergence_2026-10-11.md`; this repair does
not claim complete spelling parity.
