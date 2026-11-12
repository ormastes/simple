# Stage3 mir-lower: enum construction payload type mismatch family after Nil-is-unit (2026-11-13)

**Status:** OPEN (observed 2026-11-13 ~05:50 KST, aarch64 Linux, s3j/J2 lane stage3, pinned 3a0aac3773a)
**Area:** HIR type identity of Nil/Unit vs enum struct-variant payload typing in MIR lowering
**Introduced by:** `6bfa14881e1` "fix(hir,lint): Nil is the unit type; Nil? rejected; nil admitted
as its value" (2026-11-12 23:12) -- its own message records "Native proof (MCP build with a
rebuilt Phase 2 compiler) pending". The J2 stage3 self-build IS that pending native proof: FAIL.

## Symptom

Stage 3 self-build (stage2-admitted compiler from 3a0aac3773a building the same tree): MIR
shard processed all 1650 modules, `passed=0 sealed_failed=1650`, worker exit 1, "MIR shard
aggregate failure; link and artifact publication blocked". Distinct mir_errors:item messages
(all enum-payload or match-shape; full lines in the stage3-native-build.log):

- `match has multiple wildcard arms (arm 1)` in
  `compiler.backend._MirToLlvm.core_codegen...translate_function_with_ir_handle_impl`
  (module compiler.backend._MirToLlvm.core_codegen)
- `enum construction 'compiler.common.driver_compile_result.CompileResult.CodegenError':
  payload type mismatch at 0` (compile_to_vhdl, plugins.backend_vhdl.driver.driver_aot_vhdl_output)
- `enum construction 'CompileResult.Success': payload type mismatch at 0` x2
  (_cranelift_execute_smf, _cranelift_jit_run; static_backend_cranelift_jit_lane)
- `enum construction 'compiler.frontend.parser_types_expr.ExprKind.StringLit':
  payload type mismatch at 1` (convert_flat_expr, _FlatAstBridge.convert_nodes)
- `enum construction 'compiler.hir.hir_definitions.HirExprKind.Break':
  payload type mismatch at 0` x2 (lower_hir_expr / lower_hir_stmt)
- `enum construction 'HirExprKind.CustomBlock': payload type mismatch at 1`
  (hc_dec_hir_expr_kind, generated/hir_codec)
- `enum construction 'HirExprKind.MethodCall': payload type mismatch at 1`
  (lower_accessor_read, accessor_forwarding)
- `enum construction 'HirExprKind.StringLit': payload type mismatch at 1`
  (remap_declaration_default_expr_v1)

## Mechanism hypothesis

6bfa14881e1 makes bare `Nil` resolve to `HirTypeKind.Unit` after symbol lookup. The enum
payload-type check in MIR lowering compares the payload type recorded at the variant
declaration with the type computed at the construction site; if one side routes through the
new Nil->Unit resolution and the other side has a cached/serialized spelling of the payload
type (or computes Unit via a different path), the identity comparison fails with "payload
type mismatch at N". The seed-built compiler (which built stage2 from the same sources with
the same commit) handles both sides consistently; the self-hosted stage2 binary diverges --
the classic fixpoint-breaking pattern. HirExprKind.{Break,StringLit,MethodCall,CustomBlock}
payloads plausibly include unit-typed fields (e.g. Break payload, StringLit span-ish units).

## Why s3gen (older pin df719eff44cf) did not show this

That pin predates 6bfa14881e1: its stage3 mir-lower ran 1626/1626 with 0 fatal errors
(attempt I #2 got to idx 1570+ before the codegen Unknown-origin abort, a different defect
fixed/diagnosed separately in unknown_call_origin_driver_hir_archive_stage3_2026-11-13.md).

## Repro

J2 lane: `build/bootstrap-jgen/stage3/aarch64-unknown-linux-gnu/stage3-native-cache/.../stage3-native-build.log` — grep `mir_errors:item`. Deterministic shape expected; rerun on the same pin would re-collect.

## Next

1. Read the payload-type check in MIR lowering (enum construction verification) and the
   Nil->Unit resolution order; find the identity asymmetry.
2. Likely fix: canonicalize BOTH sides through the same Nil/Unit normalization before the
   payload comparison (or key payload typing on HirTypeKind rather than spelling).
3. Consider aHIR-level unit-type alias table so `()` and `Nil` share one canonical identity.
4. After fix: K lane (re-pin, stage2, stage3) -- scripts already staged as run-k-stage2.sh /
   run-k-stage3.sh in the jgen worktree.
