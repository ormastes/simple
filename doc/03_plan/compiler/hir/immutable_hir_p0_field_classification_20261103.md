# P0 HIR field classification and construction hazards

Inspected source: **`2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d`**, the merged
PR #5973 governing-plan revision, in `/tmp/simple-targethir-foundation-20261103`.
This is a source inventory, not P1 freeze implementation or runtime evidence.
No compiler fields were moved, no source/test files were changed, and no
compiler, generator, bootstrap, benchmark, or native test was executed.

Governing document:
[Immutable HIR / TargetHIR / MIR plan](immutable_hir_targethir_mir_refactor_plan_2026-11-03.md),
especially §§0, 2, 4, 5, 7 and P0 in §8. The prior experimental host-view and
broad cross-target worktrees are not sources for this inventory. In particular,
the inspected revision has neither the experimental `TargetWord` HIR variant
nor the experimental nominal representation fields.

## Classification rules

- **S — semantic core:** source meaning, resolved semantic identity, diagnostic
  provenance, or semantic validation evidence. A semantic result can already
  be target-constrained; S does not by itself prove portability.
- **C — semantic target constraint:** explicit requirements, alternatives,
  observed target-dependent semantic decisions, or deferred obligations.
  These remain attached to the semantic snapshot or its constraint owner;
  they must not be deleted merely because TargetHIR exists.
- **R — resolved target/lowering value:** actual layout, ABI, selected target
  branch, backend legality or emission policy. Future target-bound resolution
  belongs in TargetHIR or later MIR/codegen, with exact provenance.
- **U — unresolved provenance/classification:** the carrier alone cannot
  distinguish source intent from a baked-in decision, or the required witness
  is not retained. U blocks a portable/frozen admission claim; it does not mean
  “use the host” or “assume target independent.”

Mixed entries below classify payloads separately, rather than proposing that a
whole record move to another layer. No physical field relocation is approved.

## HirModule: all declared fields

Declaration: `src/compiler/20.hir/hir_types.spl:24`.

| Fields | Class | Required interpretation |
|---|---|---|
| `name`, `path` | S | Module/source provenance. Path normalization and identity rules remain existing owner responsibilities. |
| `imports`, `exports`, `domain_blocks` | S+C/U | Selected semantic import/export graph and raw domain declarations. Target-dependent parsing/import selection requires observed-read witnesses or a constrained variant; empty target metadata cannot make this portable. |
| `symbols` | S+C/U | Module-local semantic identities, scope and type bindings. Mutable `SymbolTable` is not frozen storage. Resolved target-dependent binding requires its semantic witness. |
| `functions`, `classes`, `structs`, `enums`, `bitfields`, `traits`, `impls`, `constants`, `static_asserts` | S with nested C/R/U | Declaration inventories; classify nested fields below. A selected or evaluated constant/assertion is not automatically reusable across targets. |
| `gpu_function_targets`, `gpu_function_backend_orders` | C, with U for selection provenance | Duplicated GPU declaration requirements/order. Function and SymbolTable copies must agree. A concrete backend selected from `auto` would instead be R and needs a recorded decision. |
| `aop_advices`, `di_bindings`, `arch_rules`, `mock_decls` | S+C | Source-observable weaving, binding and architecture policy. Their predicate text/reference names are semantic inputs, not resolved machine offsets. Target-dependent effects require witnesses. |
| `types` | S/U | Text type inventory, not a typed layout table. Reconciliation with symbol/declaration inventories must be specified before freeze. |
| `extend_enums` | S+C | Open/closed constructor-universe declarations and provider payload identities; retain closure and provider evidence. |
| `representation_declarations` | S+C/U | Assurance representation manifests, not permission to infer a native field layout. Existing codec explicitly refuses a nonempty inventory; no portable serialization claim. |
| `nogc_strict` | S | Explicit source-module contract; not an ambient target default. |
| `nogc_param_effects_checked`, `nogc_param_effect_symbol_ids`, `nogc_param_effects` | S validation evidence | Published strict-effect result and module-local correspondence. Freeze must occur after the accepted producer, with consistent lengths/IDs and no subsequent mutation. Flags alone do not prove the producer ran. |

There is **no `target_context` field** in this `HirModule`. That absence is not
evidence that the stored module is target-independent. Import/type/constant
decisions can already have consumed a target.

## HirFunction and source attributes

Declaration: `src/compiler/20.hir/hir_definitions.spl:67`.

| Fields | Class | Required interpretation |
|---|---|---|
| `symbol`, `name`, `visibility`, `is_public`, `span`, `has_doc_comment`, `doc_comment` | S | Identity, visibility and source/diagnostic metadata. Symbol IDs remain module-local. |
| `type_params`, `params`, `return_type`, `body` | S+C/U | Semantic template/signature/body; defaults and nested guards remain semantic content. Public signatures that depend on ABI/target require constrained HIR or verified symbolic obligations. |
| `effects`, `verification_contract` | S+C | Language effects, requires/ensures/decreases and proof uses. Target/runtime availability can constrain fulfillment; effect declarations are not physical calling conventions. |
| `is_async`, `is_static`, `is_method`, `is_mutable`, `is_const`, `is_extern` | S | Declaration semantics. How async state, receivers or extern calls are represented is a separate R decision. |
| `has_suspension` | S derived fact/U | Semantic body property. Inspected source constructors initially set false; the freeze boundary must identify the authoritative analysis/update, not assume the default proves absence. |
| `func_attr` | Mixed S/C/R/U | Attribute payload classification below; do not move the whole record. |
| `has_export_attr`, `export_attr` | C plus S name | C-export requirement and requested external name. Actual registers, aggregate ABI class and symbol/object conventions are R. |
| `has_driver_manifest_attr`, `driver_manifest_attr` | S+C | Declared driver/native-library identity, IDs, version and ABI requirement. Concrete runtime/provider linkage is R. |
| `has_vhdl_metadata`, `vhdl_metadata` | S+C | Hardware/generic/clock/reset/return-field contract. Scheduling/legalization and emitted device representation are R. |
| `is_gpu_kernel`, `gpu_target`, `gpu_backend_order` | S+C/U | Source kernel designation, requested capability and backend preference. Inspected producers copy `FunctionAttr`/flat declaration metadata; no evidence here that every producer preserves request-versus-selection provenance. |
| `is_generic_template` | S | Template status; not target specialization or evidence that a concrete instance is immutable. |
| `cfg`, `cfg_group`, `cfg_arm` | C | Retained guard chain identity and predicates. The selected arm is R when semantic deferral is valid. If parsing/binding already selected a branch, that decision is a semantic variant constraint instead. |
| `extern_runtime_value_abi` | S+C/U | Retained runtime-value wire contract on an extern declaration; must survive clone/codec. It is not a register assignment. Runtime/platform variation and producer authority need an explicit admission rule before general reuse. |

`FunctionAttr` lives in `00.common/_Attributes/decl_attrs.spl:667`:

- S: `is_noreturn`, `is_alloc`, `is_no_alloc`, `has_fast_math`,
  `is_volatile`, `is_no_reorder`; these alter permitted behavior/effects.
- C: `is_entry`, `is_naked`, `is_interrupt`, `is_boot`, `section`, `align`,
  `is_global`, inline/SIMD directives (`is_inline`, `is_simd`, `simd_enable`,
  `simd_disable`, `simd_prefer_scalable`), `optimization_req`, GPU fields,
  FPGA `unroll_factor`/`pipeline_ii`/`memory_banks`, and `is_rt_hal` plus
  comparison requirements. These are requests/requirements, not a legal
  instruction sequence, native register set or satisfied optimization result.
- S diagnostics: `rt_hal_error`, `placement_error`. Preserve their producing
  source/validation contract; an empty string is not a target legality proof.
- R/U: trailing `is_comdat_instance` is documented as generated instance
  emission policy, never set by source attributes. Its complete producer and
  target/object-format dependency must be identified before snapshot admission.

## HirExpr and statement payloads

`HirExpr` at `hir_definitions.spl:581` has only `kind`, `has_type_`, `type_`,
and `span`. `has_type_` is the authoritative flat presence bit: an absent type
does not make the placeholder payload authoritative.

| Carrier/payload family | Class | Boundary |
|---|---|---|
| Literals, operators, aggregate values, control flow, ownership operations, symbols/calls, contracts and source spans | S+C/U | Keep semantic operation and typed identity. A folded target-sensitive constant or resolved conditional binding requires its observed semantic constraint. |
| `type_` when present | S+C/U | Resolved semantic type, not physical `MirType`; see type provenance limitation below. |
| `CfgSelect(conds, arms, else_)` | C + S bodies | All retained alternatives remain part of the semantic input; selected arm is target-bound. This carrier does not prove that source-level imports/declarations were preserved. |
| `InlineAsm`, `InlineAsmMatch`, statement `AsmAssert` | S+C | Templates, operand expressions, explicit register/ABI constraints, target specs, wildcard/compile-error arms and ordered alternatives remain requirements. Chosen arm, actual clobber/register legality and instruction emission are R. |
| `HostGpuLane(lane_code, payload_size, marker, body)` | S+C; not inferred R | Inspected producer maps source `host`/`gpu` to 1/2 and reads literal `max_packet`/single literal payload bound. `payload_size` is therefore a source bound at this producer, not measured native layout. Zero/default cases need validation; other producers remain an audit question. |

`HirAsm`/`HirAsmConstraint`/`HirAsmMatchArm` at lines 869–917 explicitly
retain source template, volatility, constraints, clobbers, clobber ABI sets,
options, target spec, operand/output expressions and compile-error content.
Do not erase explicit physical register spellings from HIR: they are source
constraints; resolving whether they are legal is the R operation.

## HirType, generics and effects

`HirType(kind, span)` is at `hir_types.spl:672`; its variant universe is at
line 678. At this pinned revision:

- S: `Int(bits,signed)`, `Float(bits)`, `Bool`, `Char`, `Str`, `Unit`,
  tuples/arrays/slices/dictionaries, refs/pointers, Optional/Result/Union,
  nominal `Named(symbol,args)`, `DynTrait`, function types/effects,
  `TypeParam`, `Projection`, `Isolated`, `Unique`, `Shared`, `Weak`, `Never`
  and `Any`, subject to complete semantic type/identity validation.
- C: tensor dimensions/device requirements and layer shapes; pointer and
  reference semantics also carry a deferred layout obligation. Native size,
  alignment, encoding, device legalization and calling convention are R.
- Builder/error state: `Infer(id,level)` and `Error` are not automatically
  freeze-ready types. Admission needs a named rule for unresolved inference,
  erroneous regions and generic symbolic obligations; no nil/default recovery
  may be promoted to Ready.
- **U, demonstrated loss:** `HirType.named` (`hir_types.spl:786`) and HIR
  annotation lowering (`hir_lowering/types.spl:1327`) map `usize` to
  `Int(64,false)` and `isize` to `Int(64,true)`. No `TargetWord` variant exists
  here. A resulting 64-bit integer cannot reveal whether it came from a
  fixed-width source integer or a target-width spelling. This is not a
  portable 32/64-bit proof; preserve a constrained variant or repair the
  symbolic provenance in a later phase before cross-width reuse.

`HirTypeParam.symbol/name/bounds/has_default/default/span`,
`HirParam.symbol/name/type_/has_default/default/span/is_mutable`,
`is_generic_template`, `has_specialization_of`, `specialization_of`, and
`type_bindings` on class/struct/enum/trait records are S semantic template or
typed-instance facts. Bounds/defaults and concrete semantic substitutions
stay with HIR. Per-target instance layout, ABI and object specialization are
separate R artifacts. `HirTypeBindings` is a mutable dictionary alias, not a
frozen instance map. `HirImpl` method-return name/array/optional maps are
derived semantic/provenance aids; names alone must not authorize physical
layout or foreign SymbolId reuse.

`Effect(kind,span)` and `EffectKind` at `hir_types.spl:902` retain Pure, IO,
Async, Throws(type), Mutates, Allocates and Custom(name). These are S, with C
where runtime/OS availability is a semantic requirement. Effect inference and
strict-effect receipts must be finalized consistently before freeze. Actual
runtime dispatch/ABI lowering is R; neither `Custom` text nor a checked flag
proves portable capability availability.

## Layout declarations versus layout results

| Actual carrier | Class and source evidence |
|---|---|
| `HirClass`/`HirStruct` identity, fields, visibility/docs, methods and generic metadata | S; generic and nested field rules above. |
| `has_layout_attr`, `LayoutAttr.layout_kind/has_explicit_align/explicit_align/is_packed/is_preserve_order/is_compactq` | S+C source layout policy. The inspected producer calls `parse_layout_attrs`; none is an actual computed field offset. |
| `has_platform_attr`, `platform_has_error`, `platform_has_warning`, `platform_diagnostic_message`, `platform_diagnostic_line` | C presence plus S parse/validation diagnostics, **not a selected platform layout**. `platform_attr_fields_for` summarizes variants/diagnostics without retaining their complete predicates in these fields. U: prove where complete alternatives survive before claiming reusable platform obligations. |
| `PlatformPredicate` CPU/OS/ABI/bit predicates and `PlatformVariant` explicit size/alignment hints | C declared alternatives in `30.types/_TypeLayout/layout_core.spl:50`; a selected variant/validated effective layout is R. Their existence as types does not prove every HIR producer retains them. |
| `HirField` name/symbol/type/default/visibility/volatile/span | S; `has_bits_attr/bits_width` and `has_fixed_address/fixed_address` are explicit C requirements. A requested fixed address is not a chosen allocator result. |
| `HirBitfield.backing_type`, field type/width/reservation intent | S+C. `HirBitfieldField.bit_offset`, reordered field inventory and `HirBitfield.total_bits` are precomputed representation results with **U provenance**. The HIR producer sorts widths and uses a literal `word_bits = 32` before publishing offsets (`declaration_lowering.spl:925–990`). Establish whether that is language-mandated packing or target policy; do not silently relabel it portable or move it. |
| `HirEnum.runtime_name`, attributes, open-constructor flags | S identity/C representation contract. Inspected runtime name uses defining module + declaration name, not a native address. Repr attributes remain semantic constraints; payload ABI is R. |
| `FieldLayout.offset/size/align/bit_offset`, `TypeLayout.size/align/fields/stride` | R computed results (`layout_core.spl:179–200`), outside the primary HIR records. Field name/type and declared bit width are source references within the result. Future TargetHIR authority must bind exact parent/type/target, not just copy numeric fields. |

## Constructor, clone, schema and admission traps

| Concrete source seam | Trap and required later check |
|---|---|
| `hir_types.spl:49`, `hir_definitions.spl:103` and other trailing-field comments | Existing bootstrap construction relies on stable field positions/defaults. Inserting or reordering a field can shift partial named construction. Prefer the external snapshot owner; append only where compatible and verify actual constructors. |
| Flat `has_*` + payload fields on functions, expressions, parameters, fields and asm arms | These are not interchangeable with boxed `Some(payload)`. Preserve presence bits, payload type and reader convention through constructors and serialization. |
| `hir_lowering/_Items/module_build.spl:684,838`; `declaration_lowering.spl`; `class_declaration_lowering.spl` | Primary explicit constructors must retain every admitted semantic field and finalize duplicated GPU/effect metadata. Defaulted omissions are not evidence of intentional empty semantics. |
| `hir_types.spl:371` `SymbolTable.module_snapshot()` | Containers are moved by reference; subsequent lowerer reset is the documented ownership assumption. This is neither deep copy nor alias revocation. All nested dictionaries/scopes remain part of P1's freeze problem. |
| `35.semantics/resolve.spl:275,349,874` | Explicit module/function/expression reconstruction. Adding metadata needs a retention audit at every reconstruction; `has_type_` and module-local IDs must remain authoritative. |
| `35.semantics/aspect_weave.spl:162,193,200` | Spread-copy function reconstruction changes bodies and writes module inventory. Freeze must occur after the intended weave, or produce a new semantic artifact. Struct spread does not establish deep independence. |
| `30.types/type_infer/typed_module_owner_v1.spl:223–230` | Restricted typed-module producer deliberately clears params/type params/effects/cfg and many module inventories. This is a scoped producer, not a general whole-HIR cloner; prove its accepted input subset before reuse. |
| `35.semantics/value_struct_layout.spl:77–113` | Layout snapshot keeps only struct symbols and shares the passed struct inventory; other fields are empty. It is a projection with its own purpose, not a lossless/frozen module snapshot. |
| `50.mir/_MirLowering/bootstrap_globals.spl:302`; `80.driver/driver_bootstrap.spl:234`; `80.driver/driver_hir_pipeline_lowering.spl:2006`; MIR synthetic function constructors | Synthetic/partial module and function producers need explicit admission categories. Never infer complete/portable semantics from absence of fields they never populated. |
| `hir_symbol_table_methods.spl:373` renamed-symbol construction | Symbol reconstruction must preserve defining owner, generic count, type and declaration kind; the same integer in two tables is not the same identity. |
| `20.hir/generated/hir_codec.spl`, `src/app/compiler_schema/codec_gen.spl` | Generated constructor/enum-field order is authoritative. Do not hand edit; update generator/schema/version and run actual encode/decode/consumer equivalence before admitting new records. |
| `hir_codec.spl:42,69,92` | Current normal domain is v14; canonical v5 explicitly refuses as `canonical_codec_generator_stale`. Nonempty representation manifests are also refused. P1 cannot silently use unavailable canonical bytes as snapshot authority. |
| `20.hir/generated/hir_visitor.spl:923` | `walk_hir_module` currently walks only `extend_enums`, not function/record/constant dictionaries. A “visited module” result is not complete deep validation. Root coverage must be explicit and generator-owned coverage repaired/verified before relying on it. |
| `src/app/compiler_schema/registry.spl`, `visitor_gen.spl`, `spec/compiler_schema/transitions/hir_expr_to_mir.sdn` | Variant registries, generated visitors/codecs and transition dispositions must evolve together; unknown/unsupported variants cannot silently receive an overlay default. Explicit named owner imports in `hir_definitions.spl` are required for declaration payload origin materialization. |

## Open classification decisions and P0 outcome

1. Recover or constrain lost `usize/isize` provenance before cross-width HIR reuse.
2. Decide bitfield packing ownership from the language contract and real
   consumers; current hardcoded 32-bit packing is not a portability proof.
3. Locate complete platform-layout alternatives/read witnesses beyond the
   summarized HIR diagnostic fields. Do not manufacture obligations from flags.
4. Audit every GPU/backend-order, `has_suspension`, runtime-value extern ABI and
   COMDAT producer to distinguish request, semantic validation and emission
   decisions. The reviewed constructors are not the entire producer universe.
5. Define freeze-ready treatment for Infer/Error/absent types, partial/synthetic
   modules, semantic projections and checked-effect receipts.
6. Define the owner and lifecycle of target-dependent constants, imports,
   specialization and woven semantics; record positive and negative reads.
7. Verify complete generated root/child coverage and byte/native consumer
   equivalence. Source inspection and codec field presence are not execution.

This document fills the P0 **field-classification inventory** for the inspected
primary carriers and records remaining decisions. It does not close P0 runtime
baseline or all-producer audits, freeze P1 APIs, establish deep immutability,
admit a TargetHIR overlay, or prove the requested cross-compilation matrix.
