# C36 tracker optional pointer constant workaround (#3016)

Source baseline: aeb2517fac0a3f287aed4347d75235ac8976161d. Producer C36:
5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235.
Bug registered before edits: https://github.com/ormastes/simple/issues/3016.

Actual tracker consumer passed HIR 11/11 and MIR 11/11, then native 10/11.
Retained `message.module.ll:1272`, function `instantiationtracker_metadata_snapshot`,
block bb26, contains `%l278 = add ptr 3, 0`. This is the absent payload branch
for `if val entry = source.build_metadata` (baseline tracker.spl:138).
Only one invalid `add ptr` appears in the retained tracker module.

`_MirLoweringExpr/expr_dispatch.spl:5553` (ExistsCheck) emits
`emit_const(result_local, MirConstValue.Int(3), result_type)`; optional record
payload provenance makes result_type pointer-like. SSA gives the absent value
local 278 and stores it into entry slot 154. `_MirToLlvm/core_codegen.spl:1968`
emits integer `add` using pointer llvm_ty, which LLVM rejects. This trace is
source plus retained LLVM evidence; no serialized MIR dump was available.

The narrow source workaround uses explicit Some/nil match arms. The nil arm
retains absent build metadata; the Some arm reconstructs exactly the same record
and copies both mutable nested arrays. Two same-class optional record bindings
in the real snapshot fixture use the same workaround. Integer/array optional
bindings are unchanged. The fixture additionally checks absence and preserved
scalar record fields, while retaining nested-array independence assertions.

Validation pending: source review and changed-target native object/manual replay
owned by the manual qualification lane. Do not claim native success from source
inspection. No compiler change or full build is included. #3016 stays open until
a permanent compiler repair is verified, including valid pointer nil materialization.
