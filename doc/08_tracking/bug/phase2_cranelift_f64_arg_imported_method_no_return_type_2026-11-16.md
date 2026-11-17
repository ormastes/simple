# Phase-2 Cranelift: f64 argument to an imported method without `->` is refused, and the refusal kills the codegen worker

Status: OPEN against the frozen Phase 2 compiler (pin 18a1f28937c2). Current
`release/1.0.0` source carries a broader fix for defect 1 and a fix for defect 2
(established by reading the source; not re-run, no builds were done for this record).

## Symptom
Frozen Phase 2 (pin 18a1f28937c2), Cranelift backend, compiling the Stage 3 compiler
closure (1,542 modules). HIR and MIR pass; the codegen worker then prints

    E-BACKEND-CRANELIFT-CALL-ABI: compiler.hir.hir_codec_support.HirCodecWriter.put_f64: callee signature unknown; arg 1 is f64 and cannot be passed through the all-i64 import

and the worker process dies with exit -1073740791 (0xC0000409, fast-fail). Because the
whole worker dies, `--keep-going --go-to-end` does NOT continue past it: one bug per
~3.5 h round.

## Source location
- Call site: `src/compiler/20.hir/generated/hir_codec.spl` (`w.put_f64(b_value)`).
- Callee: `me put_f64(v: f64):` at `src/compiler/20.hir/hir_codec_support.spl:496`
  (no `->`). Same shape: `semantic_canonical_write_f32_v1` / `semantic_canonical_write_f64_v1`
  at `src/compiler/00.common/cache_contract/semantic_canonical_stream_v1.spl:373,375`.
- Error text built in `cl_import_call_abi_error`,
  `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:2144` ("callee signature
  unknown; arg N is f64 ...").

## Cause (hypothesis, consistent with the code comments)
An imported method without `->` has no callable type on its surface symbol, so MIR
attaches no declared params to the FuncPtr; Cranelift then cannot tell the f64 arg is
legitimate and refuses it rather than pass it through the all-i64 import.

## Workaround (VERIFIED, round 3: all 1,429 units compiled, 0 failed)
Build-tree only: give the f64-taking methods an explicit return type, e.g.
`me put_f64(v: f64) -> i64:` returning 0, and the same for
`semantic_canonical_write_f32_v1` / `semantic_canonical_write_f64_v1`.

## Does current source fix defect 1?
Probably yes, by reading, on origin/release/1.0.0:
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:6521-6544`. The comment
block (6522-6525, "hir_codec.spl `w.put_f64`") describes: when the surface symbol has no
type (`not sym_type_present`), take the provider-prescanned receiver-tail params via
`bootstrap_method_receiver_tail_params_lookup_v1(name)` (defined
`src/compiler/50.mir/mir_data.spl:2864`), receiver = i64 handle word, return stays i64;
else fall back to `callable_abi_declared_params_v1(name)`; and a later block (6546-6560)
prefers `declared_param_types_v1` on the imported symbol.

Caveat: the pin ALREADY contains the first mechanism (pin `method_calls_literals.spl:6488`,
`mir_data.spl:2860`), yet the failure occurred on it. So the pin's version of that
mechanism did not cover this call (hypothesis: the receiver-tail registration was not
populated for `HirCodecWriter.put_f64`, or the generated-module call took a different
path). The abi_declared / `declared_param_types_v1` branches are post-pin additions
(diff pin..head: `method_calls_literals.spl` +91, `mir_data.spl` +/-58). Not verified that
they cure this exact call; the workaround above remains the only verified cure.

## Defect 2: an E-BACKEND error aborts the whole worker
Pin: `cranelift_codegen_adapter.spl` (pin lines 1741-1743, 1843-1846) calls
`panic("... E-BACKEND-CRANELIFT-CALL-ABI ...")` after the JIT-only refusal hook, which
aborts the single codegen worker and marks every module failed.

Current source: fixed for the AOT lane. The refusal is now recorded and lowering goes on
(`cl_aot_refuse_call_abi`, `src/compiler/70.backend/backend/cranelift_runtime_imports.spl:94`;
rationale comment at 69-82: "the old panic aborted the single codegen worker and marked
every module of the build failed"). Call sites `cranelift_codegen_adapter.spl:1828-1830`
and `1911-1913` emit a placeholder and the AOT entry fails only that module. The `panic`
at `:1831` / `:1915` remains only as the fail-closed path when no AOT record is open for
the module handle, so the process can still abort in that residual case.

## Status
Open on the frozen Phase 2 pin. Defect 2 fixed in current source; defect 1 believed
fixed, unverified by execution.
