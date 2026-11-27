# Native-build: per-module HIR/validation/semantic-pass scratch is never freed (2026-10-24)

Bug id: `native_build_hir_phase_scopes_2026_10_24`
Follows: `native_build_per_worker_baseline_rss_2026_10_24.md` (item 3 "Not fixed"), same producer and probes.

## Symptom
Each MIR shard worker re-runs parse -> HIR -> validate -> semantic passes -> mono before lowering
its first module and sits at ~25-29 GB (after mono root discovery + the scoped cold-receipt encode).
Pre-mono growth is ~10 MB/module; measured per phase at 472 modules: HIR loop 3.4, validate 1.0,
enum-contract window 1.3 MB/module. The runtime has no GC/refcount, so all unscoped scratch is immortal.

## Constraint that decides placement
The runtime has ONE transient scope slot per thread (`rt_transient_array_scope_begin` refuses while
one is active, `runtime_native.c:1801`). The retained HIR loop body already opens scopes in
`lower_retained_surface_module`, `hir_cache_load` (refusal => cache MISS), `hir_cache_store`
(refusal => no store) and `hir_module_encode_retained_v1`. Wrapping a whole loop iteration would
silently disable the HIR cache and leak the blob encode into the outer scope. So only the steps that
are currently unscoped get scopes, each one checks `transient_array_scope_state_v1() == 0` first,
and every persistent write (ctx.add_error/add_warning, ctx.validation_* pushes, hir_modules
write-back, log_phase) is hoisted after scope end.

## Changes (one commit per phase; all source-only, take effect after a Stage 2 rebuild)
| phase | scoped (result promoted) | hoisted out | opt-out env | default |
|---|---|---|---|---|
| enum-contract window (`driver_hir_pipeline_passes.spl`) | per module: `collect_module_any_escape_receipt_v1`, `collect_module_enum_contract_receipt_v1`, `collect_module_representation_receipt_v1` (receipt); `representation_bind_module_facts_v1` (declaration list) | `publish_module_typecheck_receipt_v1`, `out` push, `hir_modules[name] = module`, `record_pass_receipt` | `SIMPLE_HIR_SEMANTIC_PASS_SCOPE=0` | on |
| validate (`driver_hir_pipeline_support.spl`) | whole-closure: layout report, `validate_layer_eq_types`, `validate_effect_contracts`, `validate_aspect_contracts` | warning/census publication, `errors` pushes, log_phase | `SIMPLE_HIR_VALIDATE_SCOPE=0` | on |
| HIR loop (`driver_hir_pipeline_lowering.spl`, retained path) | per module: `value_struct_layout_declarations_v1` (projection, promoted in the same frame); `hir_module_has_rt_hal` + `rt_criticality_claim_keys().len()` (scalars, nothing promoted) | `validation_module_values` push, `ctx.validation_module_has_rt_hal/claim_counts` pushes | `SIMPLE_HIR_LOOP_AUX_SCOPE=0` | on |
| mono constants (`40.mono/monomorphize_integration.spl:~546`) | not a scope: under root discovery an initializer with no mono-relevant node is kept instead of rebuilt (same soundness argument as `mono_root_is_relevant_v1`) | - | `SIMPLE_MONO_CONST_DISCOVERY=0` | on with discovery |

Every scope falls back to the unscoped call with a `WARNING ... UNSCOPED` line on refusal or failed
promotion (same discipline as `borrow_check_module_scoped_v1`).

The collectors and validators were checked for writes: no file-level `var` in `35.semantics/{any_escape,
enum_contract,representation_boundary,value_struct_layout,layer_eq_validation,effect_validation,
aspect_validation}`; they only READ the aspect/layer-eq/effect claim registries.

## Skipped, and why
- **HIR lowering itself**: already scoped (`lower_retained_surface_module`); its per-module growth on
  a cache HIT (no lowering at all) is the same ~2.8 MB/module as on a miss, so most of the "HIR loop"
  number is the live, retained HIR module plus the owners lowering promotes, not scratch.
- **RT-criticality validation**: already scopes each blob decode, and `rt_bound_manifest_clear()`
  assigns a global array; enclosing it would leave that global dangling.
- **Advice weaving / nogc param-effect admission**: both write rewritten modules into
  `hir_modules`/`ctx` (their output IS persistent module copies).
- **Mono `rewrite_function` (:1043) and the constant rewrite as a scope**: the walk writes
  `spec_queue`, `specialized_functions`, `spec_module`, `spec_display`, `diagnostics`, `stats`,
  `module_symbols` and leaves `self.env` for the constant pass. Those writes are the output; hoisting
  them needs a collect-then-apply restructure of mono. Discovery already cuts rewritten roots to ~1%.
- **MIR setup**: `prescan_module_struct_names`, `register_module_enum_inventory_v1`,
  `register_module_composite_inventory_v1` interleave reads with writes into the MIR lowerer's
  registries (keep-first semantics) and `bootstrap_default_provider_register` (global). Not hoistable
  without splitting each into compute-rows / apply-rows.

## Expected savings at 1471 modules (ESTIMATES, unverified)
No run was possible: the fixes need a Stage 2 rebuild (forbidden for this lane) and the host had
4-9 GB free (< 22 GB rule). Upper bounds are the measured phase deltas.
- enum-contract window: 1.0-1.9 GB (upper bound 1.3 MB/module; representation decls are usually empty).
- validate: 0.15-0.7 GB (the 1.0 MB/module window also holds nogc admission + RT-criticality, unscoped).
- HIR loop aux: <= 0.45 GB (projection walks only the module's own symbol table; `module_snapshot` is per module).
- mono constants: 0-0.5 GB (const initializers are a small share of mono's rebuilds).
- Total: ~1.5-3.5 GB => per-worker baseline before the first MIR module ~25.5-27.5 GB (from ~29 GB).

## Why this does not reach "a few GB"
The remainder is live state every worker rebuilds: the closure's HIR (~2.5+ MB/module), mono's output
modules (mono replaces `ctx.hir_modules` wholesale; the old dict shells stay immortal), validation
transports (`validation_module_array/blobs`), and MIR registries. Scopes cannot free live data. The
structural fixes are (a) workers load only claimed modules' HIR/MIR from the cache/archive instead of
re-running the whole frontend, or (b) fork workers from the coordinator after mono so the baseline is
shared copy-on-write. Either is needed for 10-20 workers in 100 GB.

## Verification owed
After the next Stage 2 rebuild: rerun `basemem/run3.sh` (204 and 472 hit) and compare phase-end RSS
for validate / enum_contract / mono; grep build.log for `[hir-pass-scope]`, `[hir-validate-scope]`,
`[hir-loop-scope]` WARNINGs (expected: none); go-to-end verdicts must match the A/B with all four
env opt-outs set to 0. `mono_root_discovery_determinism_spec.spl` should be re-run (it now covers
constants under discovery); UNEXECUTED here.
