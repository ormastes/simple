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

## Fix (2026-11-13)

Source alignment (branch `work/enum-payload-sites-20261113`, base `release/1.0.0`).
Each construction now passes a value of the declared payload type, so the
EXISTING Phase 2 compiler accepts it; every change is also type-correct on the
seed. Classification: (a) = source genuinely mistyped, (b) = check too strict.

| # | Site | Class | Change |
|---|------|-------|--------|
| 1 | `20.hir/generated/hir_codec.spl` CustomBlock (`value: BlockValue`) | (a) | `var f_value: BlockValue = BlockValue.Raw("")` placeholder; generator `app/compiler_schema/codec_gen.spl` `_emit_dec` emits it for the opaque BlockValue payload field (struct-component fallback unchanged) |
| 2 | `10.frontend/_FlatAstBridge/convert_nodes.spl` ExprKind.StringLit | (a)/(b) | route through existing `flat_bridge_interpolated_string` (typed `[Interpolation]? = Some(parts)`) |
| 3 | `expression_core.spl` + `statements.spl` HirExprKind.Break (`label: text`) | (a) | AST label is `text?`; `val break_label: text = label ?? ""` ("" = unlabeled, as `am_break_tag` reads it) |
| 4 | `expression_components.spl` HirPatternKind.Range (`start/end: HirExpr`) | (a) | absent bound was stored as nil in a non-optional slot; both bounds required, else HIR error + `HirPatternKind.Error` (no open-ended range pattern exists in src/) |
| 5 | `statements.spl` HirStmtKind.Let at 1 (`type_: HirType`) | (a) | the if-arm was the `HirType?` `v_hir_type`; lowered once into bare `v_annotated_hir_type` |
| 6 | `declaration_default_rewrite_v1.spl` HirExprKind.StringLit | (a)/(b) | `val remapped_interps: [HirInterpolation]? = Some(new_interps)` (expression_core.spl shape) |
| 7 | `60.mir_opt/mir_opt/outline.spl` MirTerminator.Ret(None) | (a) | inside `case None:` over a `BlockId?` subject; bare `None` there can lower as a catch-all Binding named None (expression_components.spl PatternKind.Binding arm), shadowing the builtin. Arm is now `case _:` |
| 8 | `35.semantics/resolve_strategies.spl` MethodResolution.FreeFunction (`func_id: SymbolId`) | (a) | `.?`-guarded `SymbolId?` alias replaced by `if val` binding into a typed `SymbolId` |
| 9 | `70.backend/backend/static_backend_cranelift_jit_lane.spl` CompileResult.Success x2 (`text?`) | (a) | payload was the JIT `i64` result; now `val result_text: text = "{result}"` |
| 10 | `plugins/backend_vhdl/driver/driver_aot_vhdl_output.spl` CodegenError (`text`) | (a) | `entry_error` is the i64 raw-bridge word annotated `text`; interpolated like the catalog error below it |
| 11 | `accessor_forwarding.spl` lower_accessor_read MethodCall at 1 (`method: text`) | (a), probable | loop var from an untyped array literal; typed `[text]` + `val accessor_method: text` |

**6bfa14881e1 is not causal.** The check (`50.mir/_MirLoweringExpr/enum_constructor_payload.spl`)
never lowers a type spelling: it compares the declared payload HirType against
remembered/source/MIR evidence of the argument. `None` is recognised by
expression kind (`enum_payload_is_builtin_none`, :245, accepted at :337) and
`nil` by `HirExprKind.NilLit` (:335, `HirTypeKind.Nil` arm :338 is the
lowercase `nil` type, types.spl:1542, untouched). 6bfa14881e1 only changes
`lower_type` for the spelling `Nil` (types.spl:1548 -> Unit) and `Nil?`/`Option<Nil>`
(`optional_of_non_unit` -> Error). None of the 11 declared payload types or
argument types is spelled `Nil`, and rejection 8/10/9 are i64/`T?` into a
nominal/text slot, not unit.

Check-side notes (not fixed here, no Phase 2 rebuild needed for the source fix):
`enum_payload_present_fills_optional` (:457) and the MIR fallback (:441) admit a
present `T` into `T?` only for text/class/struct/enum, so a present array into
`[T]?` (sites 2, 6) is rejected although an array is also a heap handle; and a
bare `case None:` over a typed Optional subject lowering to a Binding is a HIR
pattern-lowering hazard worth its own record.


## Parallel-lane overlap + residual sites (2026-11-13, PR #8774 follow-up)

7458f79f30d (same day, parallel lane) type-corrected 11 of the same
construction sites and 14ab345965a + c79be829a86 fixed codec regeneration
(canonical-Span source for the generator, named nil-slot refusal sites,
wire v17) -- so #8774 was rebased down to the two sites that lane did NOT
cover, plus this knowledge:

1. `src/compiler/50.mir/synthetic_driver_codegen.spl` (NOT in 7458f79f30d's
   list): `MirConstValue.Str(manifest.driver_class)` / `.vendor` --
   `DriverManifestAttr.driver_class`/`vendor` are `i64` ordinals
   (decl_attrs.spl:138-139), so the `Str(text)` payload check rejects them.
   Fixed to `MirConstValue.Int`. Verified with the pinned strict stage2
   binary (single-module compile, zero payload errors; the module's 3
   remaining errors are the MirCallOrigin lane artifact below).
2. `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` (NOT in
   7458f79f30d's list): three bare-`None:` match arms (two `match dbg_id:`
   at the function-opening emission, one nested `match value:` in the
   @naked terminator check) degraded to catch-alls in the pinned strict
   single-file lane and tripped `B5b: match has multiple wildcard arms (arm
   1)` in translate_function_with_ir_handle_impl. The on-disk upgrade-miss
   receipt (`SIMPLE_ENUM_REG_TRACE=1`): `bname='None' subject_owner=''
   candidates=4` -- four enums carry a `None` variant, so a bare-None arm
   cannot be proven a unit-variant pattern and the arm stays a default.
   Rewritten to `if val did = dbg_id:` / `if value.?:` presence forms.
   Verified: v2_corecodegen single-module compile, zero payload/B5b errors
   (RC=1 only from pre-existing lane artifacts in OTHER modules).

Strict-check facts measured on the pinned-819e3d7d4d92 stage2 binary
(single-module compiles, `SIMPLE_ENUM_PAYLOAD_TRACE=1` /
`SIMPLE_ENUM_REG_TRACE=1`):
- Bare `nil` into an optional enum PAYLOAD slot is rejected OUTSIDE unsafe:
  "nil outside unsafe into optional payload slot (declared 'LocalId?'); use
  None". `None` is the accepted spelling for optional payload slots --
  EXCEPT where a bare `None` PATTERN in an enclosing match shadows the
  identifier (outline.spl:487: `case None:` bound over a `BlockId?`
  subject made `Ret(None)` remember `named#29?` instead of `named#40?`).
- A `for x in list` loop variable carries NO remembered MIR type into the
  payload slot check (`remembered=''`), even copied through an annotated
  local. Annotating the LIST literal (`val candidates: [text] = [...]`)
  fixes the element type (15-line repros: unannotated list fails, annotated
  list passes). Interpolation (`"{candidate}"`) also works.
- An annotated val binding does NOT strip optionality for the payload check
  when the bound if-expression has an optional arm
  (`val t: HirType = if c: hir_type /* HirExpr? */ else: ...` remembers
  `HirType?`); unwrap the arm explicitly.
- `missing runtime identity for 'MirCallOrigin'` (synthetic_driver_codegen,
  3 unlocated errors): the `MirOperand.call_origin` struct-field DEFAULT
  (`= MirCallOrigin.Source`, mir_instruction_support.spl:260) materializes
  at `MirOperand(kind: ...)` constructions; the single-file compile lane
  does not register MirCallOrigin's identity for that module (same class as
  module_lowering.spl:2386's lane-dependent registration note). Present in
  pre-fix baselines too; NOT a payload-type error. Left for the K-lane
  stage3 run to confirm whether the real build route registers it.
- Pre-existing single-file lane artifacts (NOT payload-class, seen in every
  closure compile): return_type_interface_v1 "unresolved method call: get",
  persisted_graph "unresolved method call: is_none", llvm_support_matrix +
  hwir.frontend "tagged Any addition requires the admitted core-c-bootstrap
  runtime owner", and llc "Metadata id is already used" killing compiles
  after MIR in whichever module hits it first (_AstExpr.nodes, hir_codec,
  compiler.frontend.core.types).
- Codec regeneration was broken at the pin (span.spl re-export facade ->
  classify 'Span' fails); 14ab345965a pointed codec_gen at the canonical
  Span source -- regen works again (verified via a synthetic-root run of
  the pinned seed).

Verification matrix (pinned strict stage2 binary, per-module compiles, all
payload-clean for the changed modules): regenerated hir_codec (hc2),
convert_nodes (fb2), hir_lowering family statements/expression_core/
expression_components/accessor_forwarding (v_statements, v2_statements),
declaration_default_rewrite_v1 (v_mirstring), outline (v2_mirstring),
core_codegen (v2_corecodegen), cranelift jit lane (v_cranelift), vhdl
driver (v_vhdl), synthetic_driver_codegen (v2_mirstring). Codec unit specs
hir_codec_optional_enum_decoder (3/3) + hir_codec_nil_scalar_reject (12/12)
pass under the pinned seed against the regenerated codec; the two
bare-node/struct-field codec specs fail identically on the pristine pin
(zero-examples from the pre-14ab345965a classify breakage).

## Root cause found (2026-11-13, lane work/enum-payload-registry-20261113): foreign payload-registry rows in the bootstrap-fixed lane

The five-victim family (ConstValue.Array, JsonKind.Array, JsonValue.Object,
MirTypeKind.Tuple, MirOperandKind.Copy) is NEITHER the Nil/Unit class NOR
site-level mistyping (the Fix table above covers that class and its
parallel-lane follow-ups). It is a REGISTRY-OWNERSHIP defect in the
`aot:bootstrap_fixed` lane -- exactly the hazard the non-bootstrap tail
comment at module_lowering.spl step c (the old :3345-3359 block) describes.

### Lane mechanics

- Gate (driver_pipeline_lowering.spl): the entry closure contains
  `app.cli.bootstrap_main` AND `allow_bootstrap_shortcuts` (positional
  native-build) AND `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` AND
  `SIMPLE_BOOTSTRAP=1` (and not STAGE4).
- That lane builds ONE shared `bootstrap_lowering` instance and registers
  the whole closure's enums ONCE up front
  (`register_module_enum_bootstrap_inventory_v1`,
  module_lowering.spl:2401-2410; the driver comment at
  driver_pipeline_lowering.spl:1112-1122 records why: "lower_module's
  bootstrap-flat branch returns before the non-bootstrap tail, so on this
  fresh lowering instance NO enum registration exists").
- Every closure module then lowers through `lower_module`'s
  `bootstrap_mode` branch, which RETURNS EARLY (module_lowering.spl:3205+)
  -- the non-bootstrap tail's own-enum pass (clear
  `enum_registration_current[name]`, re-register `module.enums`) NEVER
  RUNS on this lane.
- The per-module provider pass cannot repair it: both dedup predicates
  (`provider_enum_row_current_v1`, `enum_registration_is_current_v1`) are
  keyed by BARE NAME and compare the recorded runtime_name, which is
  INVARIANT across a declaration's per-module HirEnum copies. Whichever
  module's copy the inventory registered LAST keeps its rows pinned for
  every later consumer. (HIR re-lowers every imported enum into each
  consumer's `module.enums` with consumer-local SymbolIds --
  20.hir/hir_lowering/_Items/module_build.spl:276-301; SymbolTable symbol
  numbering restarts per module, hir_types.spl:375.)
- Result: `enum_variant_payload_types` rows carry the REGISTERING copy's
  SymbolIds, but `enum_payload_local_compatible`
  (enum_constructor_payload.spl:326) resolves them through the CURRENT
  module's `self.symbols` and compares against the consumer's
  remembered/source types (consumer-local ids). A foreign id either misses
  `symbols.symbols.has()` (kind 0) or aliases an unrelated same-numbered
  symbol; either way `enum_payload_named_alias_equal`
  (enum_payload_type_identity.spl:18) says no. Scalar payloads are
  symbol-free (`mir_hir_type_is_symbol_free`) and pass on MIR-kind
  evidence -- which is why ONLY array/tuple/nominal payloads fail, and why
  the stage3 run sealed-failed 1650/1650 modules.

### Trace evidence (minimal in-lane fixture, stage2-admitted binary sha 197b4e93)

Fixture: a replacement `src/app/cli/bootstrap_main.spl` whose closure is
13 modules (`use`s of lib.common.json.value + compiler.blocks.definition),
plus three modules that all import `ConstValue`/`JsonValue` and construct
BOUND-VARIABLE payloads (the exact json_to_const / mapping shapes). Run:
`SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 native-build
<fixture>/bootstrap_main.spl --entry-closure --threads=1 --low-memory`
(also needs the pinned SDKROOT/MACOSX_DEPLOYMENT_TARGET vector). The fake
entry passes the bootstrap_fixed gate, so the whole probe runs IN the
failing lane at 13-module scale (~5 s with warm HIR cache).

Unpatched, traced (SIMPLE_ENUM_PAYLOAD_TRACE=1
SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1):

    [enum-payload-path] remembered module=app.cli.enumfix_m1 local=13 expected='[named#4]' actual='[named#1]'
    [enum-payload] module=app.cli.enumfix_m1 expected='[named#4]' line=8 remembered='[named#1]' source='[named#1]' mir=present
    [enum-payload] module=app.cli.enumfix_m1 expected='[named#3]' line=13 remembered='none' source='[named#0]' mir=present
    [enum-payload] module=app.cli.enumfix_m2 expected='[named#4]' line=8 ...   (m2/m3: identical foreign ids)
    [enum-payload] module=lib.common.json.value expected='[named#3]' line=85 remembered='[named#8]' source='[named#8]' mir=present

- remembered/source ids are CONSUMER-local (m1's own `[ConstValue]`
  annotation is `named#1`); the expected row was installed by ANOTHER
  module's copy (`named#4` does not resolve to ConstValue in m1's table).
- Even the DECLARING module reads a foreign row for its own enum:
  lib.common.json.value's local JsonValue is `named#8`, the registry says
  `named#3` (m1/m2/m3 import JsonValue; the inventory's LAST copy wins).
- Errors byte-match the stage3 log family:
  `enum construction 'compiler.blocks.definition.ConstValue.Array':
  payload type mismatch at 0; function=trigger_m1`,
  `'lib.common.json.value.JsonValue.Object': payload type mismatch at 1`,
  plus in-module `JsonValue.Array at 0` from `_json_value_array_at`
  (mirrors the stage3 log's lib.common.json.value failures).
- Scalar control in the same functions (`ConstValue.Int(7)`, expected
  'i64') passes via mir-evidence -- the check itself is correct; the
  corruption is registration ownership.

### A/B: same binary, same sources, only registration ownership differs

- bootstrap_fixed lane (fixture entry, WHOLE_PROGRAM=1): 13 payload
  mismatches (traces above).
- DIRECT lane (same fixture entry, no WHOLE_PROGRAM -- the gate falls
  through to the shared-direct lane, whose non-bootstrap tail runs the
  own-enum pass): ZERO payload errors. Path trace:
  `remembered module=app.cli.bootstrap_main local=7 expected='[named#4]'
  actual='[named#4]'` -> `remembered-accept`. The only failing unit is
  lib.common.json.value at llc ("defined with type 'i64' but expected
  'ptr'") -- the pre-existing codegen lane artifact documented above, not
  a payload error.
- Interpretation: with consumer-local rows, expected == remembered and the
  strict check accepts these exact construction shapes. The ONLY delta
  between the two lanes' outcomes is the missing per-consumer enum
  re-registration in the bootstrap branch.

### Why the admitted stage-2 binary could not self-validate the fix

The stage2-admitted binary executes its OWN compiled-in lowering logic;
edits to 50.mir sources change only the STAGE-3 OUTPUT, not the running
checker. (Confirmed: an instrumented patch adding an
SIMPLE_ENUM_REG_TRACE receipt to the bootstrap branch printed NOTHING when
the old binary compiled the fixture.) Validating lowered-code fixes
requires either (a) the seed-rebuilt stage-2 binary, or (b) the seed's
`native-build` dispatch, which runs `native_build_worker.spl` FROM SOURCE
(`simple run src/app/cli/native_build_worker.spl ...`) and therefore
executes patched compiler logic interpreted (usable but slow: the fixture
probe did not reach MIR in 15 min).

### Fix (module_lowering.spl:3205-3244, lower_module bootstrap branch)

Port the tail's own-enum pass into the bootstrap branch, before any module
constant or function body can construct a payload:

    if bootstrap_mode:
        val bs_enum_values = module.enums.values()
        var bs_enum_i = 0
        while bs_enum_i < bs_enum_values.len():
            val bs_enum_def: HirEnum = bs_enum_values[bs_enum_i]
            self.enum_registration_current[bs_enum_def.name] = ""
            self.register_enum_variants(bs_enum_def)
            self.register_enum_runtime_id(bs_enum_def)
            bs_enum_i = bs_enum_i + 1
        ... (SIMPLE_ENUM_REG_TRACE-gated bs-own-enums receipt)

- Clearing the bare-name mark first forces the full re-registration (the
  dedup would otherwise skip; same discipline as the tail pass).
- `module.enums` holds this consumer's re-lowered imports with
  consumer-local SymbolIds, so payload rows become resolvable through
  `self.symbols`. Variant names/discriminants and runtime ids are
  identical across copies (runtime id is a hash of the invariant
  runtime_name), so emission is unaffected. The two same-named JsonValue
  enums' collision behaviour (`enum_constructor_metadata_owner` -> "" ->
  untyped route) is unchanged.
- Scope: bootstrap branch only; the non-bootstrap lane is untouched (its
  tail pass already does exactly this). Cost: O(len(module.enums)) per
  module -- the same price the non-bootstrap lane already pays per module.

### Verification status

- Mechanism + before-state: traced foreign-row ids in the failing lane
  (above), byte-matching the stage3 log family. OPEN.
- Fix discipline: PROVEN equivalent to the direct lane's tail pass, which
  ACCEPTS the same fixture with zero payload errors (same stage-2 binary).
- Compiled-mode A/B (seed-rebuilt stage-2 from the patched worktree, then
  the fixture in the bootstrap_fixed lane): seed build launched from
  /private/tmp/perf-fix-enum with the pinned f9dd7ada764 seed
  (log /tmp/enum-fix-probe/seed-build-patched.log, output
  /tmp/enum-fix-probe/stage2-patched/simple); parse-bound (~1659 modules),
  still running at handoff. NOTE: the pinned seed prints a NON-FATAL
  "workarounds: refresh failed ... unknown canonical bug ID
  riscv64_guest_result_text_payload_empty_2026_11_06" for this source
  pair and continues.
- direct-env-runtime-guard: not applicable (no new env reads beyond the
  existing mir_lower_env_get pattern already used throughout the file).

### Residual risk

1. The fix is verified by equivalence with the direct lane's proven
   discipline, not yet by a compiled stage-3 MIR run on the full closure
   (the seed build was still parsing at handoff). If the seed build
   completes, run the fixture A/B and, if time allows, one full
   bootstrap_main probe to measure stage-3 MIR progress; expect the
   payload family to vanish and possibly expose unrelated downstream
   stage-3 defects (the doc's other open families).
2. Per-module re-registration on the shared instance grows
   enum_variant_payload_types churn; the transient scope promotes the
   registries as before, but RSS on the 1650-module closure should be
   watched on the first real stage-3 run.
3. Same-named enum collisions within ONE consumer's module.enums keep
   last-wins bare rows (unchanged semantics); the strict check's typed
   path then keys off the qualified owner, and the bare collision still
   routes to the untyped constructor path -- same as the direct lane.
