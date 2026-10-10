# float(text) reached LLVM as a pointer-to-number cast

Status: rebased onto the reconciled release/1.0 cast lowering; the parse
path itself is superseded, the strict-parse guard and the invalid-source
diagnostic are this lane's remaining delta. Native fixtures and broader
gates pending on the rebased head.

Release reconciliation: `lower_cast_expr` no longer exists as the single
cast entry point. Commit `ceac0fc96a5` split `x as T` (Cast) from `T(x)`
(ConvertCall) and routed a proven text operand through
`lower_text_parse_to_numeric` (`rt_string_to_float` + `rt_value_as_float`),
which removed the original `ptr`-to-`double` LLVM failure this bug tracked.
That reconciled path unboxed the parse result WITHOUT checking the nil tag,
so malformed text silently became 0.0 -- the seed's `f64()`/`float()`
conversion is strict and errors on a failed parse. This lane's rebased
repair keeps the reconciled dispatch and adds the missing pieces:

- `lower_text_parse_to_numeric` (float branch) now checks the nil tag (3)
  before unboxing and branches to a non-returning `rt_panic`
  (pointer/length ABI) on failure, so a valid 0.0 stays distinct from a
  failed parse.
- `lower_cast_or_convert` rejects a positively-typed pointer/aggregate
  source for a float target with a fatal MIR diagnostic, instead of
  leaking a ptr-to-double cast to the backends.

Numeric casts keep their existing path; enum discriminant extraction is
untouched.

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

The coordinated compiler now includes this change. Scoped native positive/negative
fixtures passed on ARM (EM183), and explicit-source LLVM18 compilation produced
a genuine RISC-V object (EM243). Original module matrix qualification and the
isolated release head remain pending. No RISC-V execution is claimed.

The canonical parser's whitespace/hexadecimal spelling difference from the
legacy seed builtin is explicitly tracked in
`float_text_cast_parser_spelling_divergence_2026-10-11.md`; this repair does
not claim complete spelling parity.

Final scoped native qualification and exact receipts: [verification](../verification/native_text_float_cast_2026-10-11.md). Authored unit execution and standalone PR-head admission remain pending.
