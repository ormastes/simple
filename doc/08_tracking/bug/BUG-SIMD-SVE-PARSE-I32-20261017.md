# BUG-SIMD-SVE-PARSE-I32-20261017

Date: 2026-10-17. Status: source fix proposed; native qualification pending.
Authoritative DB reconciliation pending; no qualified DB tool is available.

The SVE vector-length reader in
`src/compiler/30.types/simd_capabilities.spl:453` calls text.parse_i32(), which
has no method implementation or builtin lowering in immutable producer0015.
The real MIR rejects it; a const-zero unresolved-call warning is not success.
Focused cycle two fails that module before object emission.

Use the existing pure-Simple canonical
`std.common.convert.try_parse_i32(text) -> i64?`. It delegates to a checked
signed-i32 range parser. Trim input as before, map invalid/out-of-range results
to zero, and narrow only an already range-checked i64 to i32. The existing
positive-byte guard, multiplication by eight and default zero SVL remain.
Negative, zero, invalid and out-of-range input cannot update the reported SVL.
No unchecked integer parser, custom parser or fabricated ABI is introduced.

The converter is a real additional source dependency, copied unchanged from
the same frozen15f7 source. It declares no further module imports. Final probe
exercises actual converter boundaries and invalid input and validates the
EVEX register arrays as well as the original x86 immediate cases.

Evidence: co-located-cycle2/compile.log; actual fatal source line is retained
inside the admitted source snapshot. Focused cycle three subsequently passed
MIR65/65 and emitted54 new AMD64 COFF objects after the fix. Runtime discovery
then failed because the tiny project has no src/runtime, so native behavior
and broad core qualification remain pending.
