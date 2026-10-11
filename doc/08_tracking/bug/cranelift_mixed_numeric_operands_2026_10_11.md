# Cranelift mixed numeric operands

Status: the identical native fixture passes its positive and negative controls
on LLVM and the fixed experimental Cranelift producer. Full compiler admission
and the original spec-adapter replay are separate pending gates.

The admitted producer `48975d35845f703116db796224c4c8cc13a8aa68dc0395664881f8594096fa6d`
rejects the mixed arithmetic interpreter-spec adapter during Cranelift AOT.
Its retained verifier diagnostics identify both operand orders:

```
inst24 (v18 = sdiv.i64 v15, v17): arg 1 (v17) has type f64, expected i64
inst86 (v64 = fdiv.f64 v61, v63): arg 1 (v63) has type i64, expected f64
```

Evidence: `/home/yoon/dev/phase2-six-results-20261011/cranelift-interpreter-incremental/bisect-mixed/positive-build.log`.
The same mixed numeric source passes the LLVM adapter. The enum-formatted AOT
failure obscures these underlying verifier messages; it is not an enum defect.

`cl_translate_binop` chose its floating instruction using only the left operand
and passed both SSA values unchanged. MIR preserves operand types, so the
backend must normalize them. Addition and multiplication with literals can be
constant-folded and hide the same defect.

The fix normalizes scalar floating arithmetic and comparisons to the wider
floating operand type through the existing cast emitter. Integer-only operations,
unsigned division, shifts, remainder, and runtime-dispatched operations retain
their existing paths. Integer-to-float conversion uses each operand's own
signedness; no float-to-integer coercion is introduced.

Acceptance fixture: `test/fixtures/compiler/cranelift_mixed_numeric_probe.spl`.
Compile with the rebuilt self-hosted producer, `--backend cranelift`,
`--entry-closure`, and `SIMPLE_NO_STUB_FALLBACK=1`. The normal invocation must
exit 0 and print `mixed-numeric assertions=18 PASS`; `--negative` must exit 1
and print `mixed-numeric assertion 1 failed`. Parameters prevent literal folding
from masking mixed operand handling. The original mixed numeric spec adapter
must also pass its positive and negative controls before this issue is closed.

Source validation: `git diff --check` passed. No native PASS is claimed from
that source-only check, and no compiler cache was removed or shared with a new
producer.

The fixture SHA-256 is
`9cc9503afd36ef0f805ca934f06f6faab3abfdc9eca6e7896b7acebf9ccaebd0` on both backends.
LLVM producer `48975d35845f703116db796224c4c8cc13a8aa68dc0395664881f8594096fa6d`
passed once; the unchanged LLVM test was not rerun.
Cranelift source `6bffb3135df3e938a39f5e3dba13e62cde297ce1` and experimental
producer `54f23cb2274e43f781138a7c110ebcd3a421fb958337e5624d615af6a7fe9da3`
compile the fixture successfully with default optimization. Both backend
executables exit 0 with exactly `mixed-numeric assertions=18 PASS\n`; both
`--negative` runs exit 1 with exactly `mixed-numeric assertion 1 failed\n`.
All four executions have empty stderr.

Evidence under `/home/yoon/dev/phase2-six-results-20261011/mixed-numeric-regression/`:
`llvm-result.json` and `cranelift-cycle3-54f23/result.json`, with build and run
logs retained alongside. Cranelift evidence remains explicitly experimental
until producer admission. The fixture checks integer-only signed/unsigned
division unchanged, mixed conversions in both operand orders, unsigned values
above the signed range, and f32/f64 width normalization. Same-width floating
operands reuse existing SSA values without emitted casts; only required numeric
conversions are emitted.
