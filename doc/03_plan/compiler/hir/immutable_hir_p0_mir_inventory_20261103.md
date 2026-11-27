# P0: MIR readers, context, streaming, and mutation boundaries

Date: 2026-11-03. Baseline: `4fccb94e564b25a0a2effdd711113da5a1b1e20c`, branch `work/targethir-foundation-20261103`. This is a read-only source inventory, not executable qualification. No source behavior, default gate, or runtime was changed. Experimental host-view work in `/tmp/simple-hir-host-view-20261103` is a design reference only; it supplies no baseline proof.

All paths below are repository-relative; line numbers describe this baseline.

## Entry points and compatibility contracts

| Source evidence | Current contract and migration constraint |
| --- | --- |
| `src/compiler/50.mir/_MirLowering/module_lowering.spl:508` | `MirLowering.new` constructs the legacy unknown-target context and delegates to `new_for_target`. Preserve this route; do not introduce a default strict-target rejection. |
| Same file, `:512`, `:655`, `:663` | `new_for_target` receives a symbol table and explicit target context; constructor retains context and initializes the optional compact declaration repository to nil. |
| Same file, `:1842`, `:1950` | Struct and callable prescans accept a raw `Dict<text,HirModule>` plus key. They inventory declarations, symbols, globals, layouts, callable metadata, traits, and RTI before ordinary module lowering. A gate only inside `lower_module` cannot cover these readers. Existing dictionary/key and scalar feeder transport workarounds must survive a no-behavior-change refactor. |
| Same file, `:2278`, `:2299` | Bootstrap entry and closure entrypoints take raw HIR plus provider arrays. Explicit trailing argument shapes document historical transport failures. Closure lowering delegates to the transient wrapper. |
| Same file, `:2326`, `:2606`, `:2620` | Transient wrapper, ordinary lowering, and guarded lowering all remain raw-HIR entry routes. Ordinary lowering selects declaration guards at `:2614` before calling the guarded body. |
| Same file, `:3512`, `:3554` | Emit-all and emit-function helpers also accept raw HIR; the latter additionally receives a raw function. A typed outer entry alone does not prove all readers migrated. |
| `src/compiler/50.mir/_MirLowering/archive_borrowed_module_v1.spl:33` | Borrowed archive entry consumes raw HIR inside a caller-owned active scope. Its authority and lifetime contract differs from the ordinary transient wrapper. |

`src/compiler/50.mir/mir_lowering_types.spl:614` stores `MirTargetContext`; `:683` stores the optional compact repository. There is no target-feature snapshot or typed TargetHIR field on this baseline. `src/compiler/00.common/mir_target_context.spl:144` constructs context from caller inputs; OS derivation is at `:84`, architecture normalization at `:153`, subarchitecture selection at `:160`, and collection admission at `:169`. These facts do not establish independent environment capture by the context constructor.

## Selection and ambient inputs

`src/compiler/50.mir/_MirLowering/asm_and_targets.spl:111` is the expression `lower_cfg_select` seam. At `:125`, it passes explicit `self.target_context` but reads `cfg_enabled_features()` at selection time. Declaration predicate and group selection repeat that feature read at `:149` and `:232`. Replaying a retained HIR under a context alone therefore does not establish a stable feature snapshot.

`apply_decl_cfg_guards` at `:242` builds selected declaration collections. It can return the original module when no selection changes are needed; otherwise `:361` starts with `var out = module` and replaces top-level collections at `:362–368`. This is not a deep-freeze proof for symbols, nested bodies, or shared carriers. `src/compiler/50.mir/mir_cfg_select.spl` supplies the existing target-explicit predicate evaluator, not a typed immutable-HIR reader interface.

## Mutation evidence and ownership uncertainty

`module_lowering.spl:2649` assigns `self.symbols = module.symbols`. Subsequent real writers include:

| File under `src/compiler/50.mir/` | Evidence |
| --- | --- |
| `_MirLowering/provider_metadata.spl:375`, `:385–386`, `:473–485` | Defines bindings, writes symbol records, and binds qualified types/functions. |
| `_MirLowering/declaration_default_bindings_v1.spl:113`, `:152`, `:211`, `:289–310` | Installs lexical/global/callable bindings and rewrites relocated symbols. |
| `_MirLowering/declaration_default_rewrite_v1.spl:531` | Writes relocated symbol records. |
| `_MirLowering/resident_default_global_owner.spl:68` | Defines a working binding. |
| `_MirLowering/native_trait_conversion.spl:174`; `_MirLowering/native_trait_thunks.spl:33`, `:115` | Synthesizes callable symbols. |

These establish mutable symbol work and an alias boundary requiring investigation; they do not independently prove external source mutation under every runtime transport mode. A future frozen source needs a distinct mutable task symbol owner or overlay.

Stronger direct carrier-write evidence exists in `archive_borrowed_module_v1.spl:148–157`: selected archive continuation registers preserved symbols into `module.symbols`, inserts previous scopes, and advances symbol/scope counters. Collision checks precede those writes. Preserve the continuation behavior using a mutable task overlay rather than silently removing it or relabeling the input readonly.

Nested lowering is another propagation boundary: `_MirLoweringExpr/switch_operators_calls.spl:7924` constructs a child with the parent symbols/context, `:8044` copies the raw declaration repository, and `:8185` returns child symbols to the parent. A later admission or ownership change must account for this route explicitly.

Assignments to `module.functions`, constants, or other output collections elsewhere in module lowering may refer to MIR output/builders. They are not counted as HIR mutations merely because the variable is named `module`.

## Streaming and lifetime contracts

`src/compiler/80.driver/driver_pipeline_lowering.spl:1003` prescans bootstrap modules; `:1055` lowers closure modules and `:1070` lowers the entry. Direct paths prescan at `:1183` and `:1201`; `:1484–1487` lower each available `scoped_hir` through `lower_module_transient_scoped`, handling missing HIR explicitly. Fallback paths prescan at `:1602` and lower at `:1635`. Physical ownership policy branches occur around `:1156–1179`. These are existing incremental scheduling boundaries: a migration must not impose an all-program retained-HIR or selection barrier.

Transient lifecycle in `module_lowering.spl`:

1. `:2399` begins the array scope. If acquisition fails because an outer scope is live, `:2404–2406` retains an unscoped legacy fallback; strict rejection would change behavior.
2. `:2410–2417` resets stale registry delta, begins reverse-reference batching, handles acquisition failure, and performs lowering.
3. `:2466–2482` clears scratch/provider state. `:2489–2490` removes borrowed trait providers from the promotion root while retaining a local borrowed reference.
4. `:2494–2525` pauses and promotes output, owner state, and bootstrap registry state, with abort paths on failure.
5. `:2537` ends the scope; `:2542` restores borrowed providers; subsequent reverse-reference publication has explicit error handling.

`src/compiler/50.mir/_MirLowering/transient_owner.spl` explicitly enumerates retained roots: compact repository at `:48`, enum/default indexes at `:49–55`, and provider session/method/layout state at `:181–207`. New retained frozen/view fields require a deliberate root inventory update. Retaining or promoting full provider graphs by accident would defeat streaming. Registry publication also involves `_MirLowering/bootstrap_mir_store.spl`; its mutable publication state must remain separate from immutable source ownership.

The borrowed archive entry checks an active unpaused scope at `archive_borrowed_module_v1.spl:40`, repository/provider constraints at `:42–44`, owner and declaration authority at `:47–57`, exact encoded body digest at `:61–63`, and reprojected declaration digest at `:68–72`. It delegates lowering at `:162–163`, detaches body-bearing default/capture scratch at `:167–171`, and rejects unfinished finally state at `:172–173`. It does not acquire, pause, promote, or close the caller's scope. Preserve these exact lifetime distinctions.

## One narrow future PR-D candidate

After deep freezing and typed TargetHIR construction are independently established, migrate only the expression-arm selection reader at `asm_and_targets.spl:111–125`. A default-off feature-gated adapter can consume a selected-arm read handle bound to frozen source plus target/features, then feed the existing mutable MIR block builder. Keep the raw-HIR legacy path unchanged when disabled.

Proposed acceptance: one retained HIR fixture containing fixed-i64 statement-only alternatives; explicit x86/x86_64 contexts across Linux, Windows, and SimpleOS; exact selected MIR constants; alternating forward/reverse context order; byte-identical retained HIR after every replay. Add disabled-feature behavior equivalence and mismatched-handle rejection tests. This is a proposed reader experiment, not implemented or executed evidence. Exclude declaration-family selection, compact repository admission, archive transport changes, and a whole-program switch from that PR.

## Qualification and remaining evidence

Source inspection only: no compiler build, runtime test, cross-link, execution, allocation profile, or RSS measurement was performed for this inventory. Required future evidence includes deep alias isolation, nested lowerer ownership, selected archive symbol continuation, frozen source lifetime across scope close, feature snapshot determinism, legacy disabled-path equivalence, and streaming memory bounds. No default strict gate or landing-readiness claim follows from this document.
