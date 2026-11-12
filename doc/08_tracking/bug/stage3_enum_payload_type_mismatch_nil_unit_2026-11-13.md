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

## Decisive context (2026-11-13 ~07:05): this is the 02821241513 family, not Nil-specific

`02821241513` "fix(blocks): sql/shell helpers return the SqlQuery/ShellCommands
payload types" (IN the df719eff44cf..3a0aac3773a range) records the identical
pattern: "The seed accepted it; the Windows Phase 2 MIR rejected both
constructions (payload type mismatch at 0)". So the enum-payload check is known
to DIVERGE between the seed-built compiler and self-hosted/Phase-2 binaries --
6bfa14881e1 is not the cause; it merely added more loosely-typed constructions
for the stricter self-hosted check to reject. The CustomBlock instance
(SIMPLE_ENUM_PAYLOAD_TRACE=1, 57-min single-module repro on the J2 stage2 binary):

    [enum-payload] module=compiler.hir.generated.hir_codec expected='named#63'
    remembered='named#63?' source='named#63?' mir=present
    at hc_dec_hir_expr_kind line ~5102: HirExprKind.CustomBlock(f_kind, f_value)
    with `var f_value: BlockValue? = nil` vs declared payload `value: BlockValue`
    (hir_definitions.spl:689).

The sibling error "match has multiple wildcard arms (arm 1)" in
core_codegen.translate_function_with_ir_handle_impl is the SAME class: a
match-validation diagnostic the self-hosted binary's frontend emits and the
seed's does not. Root cause is a fixpoint break in match/check evaluation
between seed and self-hosted codegen -- NOT in Nil handling.

## Fix strategy (two lanes)

A. Whack-a-mole (precedent 02821241513): align each rejected construction to
   the declared payload type (unwrap the optional at the ctor site). The
   hir_codec instance is GENERATED code -- fix the codec generator's optional
   local emission, not the file. Sites from the J2 log: hir_codec x2
   (CustomBlock, HirExprKind decode), expression_core/statements (Break),
   accessor_forwarding (MethodCall), declaration_default_rewrite (StringLit),
   convert_nodes (ExprKind.StringLit), cranelift_jit_lane (CompileResult x2),
   driver_aot_vhdl_output (CodegenError), core_codegen (wildcard arm).
B. Root cause: find the match/check-evaluation divergence (likely match-arm
   selection or wildcard handling) between seed and self-hosted codegen; that
   fixes the whole family and the "multiple wildcard arms" class too.

## Minimal reproducer (2026-11-13 ~07:20): seed vs self-hosted enum-payload check

shapes.spl: `struct Block(tag: i64)` + `enum NodeKind: CustomBlock(kind: text, value: Block) | Break(level: i64) | Empty`
use2.spl:
    fn decode(flag: i64) -> NodeKind:
        var value: Block? = nil
        if flag == 1:
            value = Block(tag: 7)
        NodeKind.CustomBlock("k", value)   # Optional local into PLAIN payload slot

Seed (`src/compiler_rust/target/bootstrap/simple`, pinned 3a0aac3773a):
RC=0 -- accepts. J2 stage2-admitted binary (same pin): RC=1
`enum construction 'shapes.NodeKind.CustomBlock': payload type mismatch at 1`.
Compile time ~0.4 s per binary. THIS is the 15-line fixpoint break.

Static reading: enum_payload_types_alias_equal((Named, Optional)) has no arm ->
falls to `case _:` -> hir_types_equal -> false -- STRICT in source. The seed's
acceptance therefore comes from an EARLIER lenient branch in the
enum_payload_compatible caller chain (enum_constructor_payload.spl) that the
seed executes and the self-hosted binary skips -- a match-arm-sensitive path,
the same class as the B5b wildcard misdiagnosis in core_codegen. The B5b error
there is collateral: enum constructor arms degrade to Wildcard when their
shape resolution misses, so a single-wildcard match reports "multiple wildcard
arms".

## Fix approach for the next lane

Differential-debug the 15-line repro: run both binaries with the payload-trace
env and MIR dumps, find the first divergent branch in the
enum_payload_compatible chain, then inspect THAT function's compiled match
lowering for the arm-selection divergence (likely candidate: or-pattern /
multi-constructor arm selection in a scrutinee-dependent match, or a
fall-through branch whose condition involves a registry lookup that resolves
differently in the self-hosted binary -- chase-family residual).

## Differential trace result (2026-11-13 ~07:40): seed never runs the check

On the 15-line repro with SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1 +
SIMPLE_ENUM_PAYLOAD_TRACE=1:
- SEED: RC=0, ZERO trace lines -- the seed lowers the enum construction via a
  route that never calls enum_payload_local_compatible (its log shows an
  "enum-contract pass: 0 diagnostic(s)" instead).
- J2 stage2-admitted: RC=1, trace shows
  `remembered module=use2 local=8 expected='named#1' actual='named#1?'`
  then strict rejection inside enum_payload_local_compatible.

So the divergence is CONTROL FLOW at the construction-lowering call site, not
data: both binaries contain the same check source, but the self-hosted binary
routes constructions through the checked path where the seed routes them
around it. The checker's strictness is a red herring -- the fixpoint break is
in the caller (emit/lower enum construction dispatch).

## Next concrete step

Seed-lane instrumentation rebuild: add eprintln tracing to the enum-
construction dispatch caller (the site that decides checked vs unchecked
route), rebuild stage2 with the SEED (~11 min, run-k-stage2.sh pattern), run
the 15-line repro, capture the seed's route. Diff against the J2 binary's
route on the same input. The diverging branch condition is the fixpoint
break; fix it, then K lane.

## REFRAME (2026-11-13 ~07:40): fixpoint between Simple generations is INTACT

Instrumented seed-built stage2 (fresh, from tip+trace patch) REJECTS the
15-line repro identically to the J2 stage2-admitted binary. The RUST seed is
the outlier that accepts. Both Simple-compiled generations agree (strict) --
the self-host fixpoint holds; the new-pin SOURCES contain enum constructions
that only the rust seed's leniency accepts (the generated codec churn from the
sdn-protocol-codec-fixes merges #8681/fe3425d0ca6 in the range is the likely
introducer of `var f_value: BlockValue? = nil` into the plain-Block slot).

Implication: NO compiler fix is needed for the bootstrap. The K lane is pure
source alignment (02821241513 precedent): fix the generated codec's optional
local emission (generator, not the generated file) plus the ~7 hand-written
sites so the declared payload types flow. The old pin passed MIR because its
codec emitted compatible shapes. NOTE: another lane is concurrently active on
the sdn enum-payload divergence (main-tree commit 671d5545201) -- coordinate
before large generator changes.
