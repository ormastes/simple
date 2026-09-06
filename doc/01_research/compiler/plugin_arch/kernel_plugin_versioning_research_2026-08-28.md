# Kernel + Pluggable Compiler/Runtime under MDSOC+: Repo Inventory and Prior Art

Date: 2026-08-28. Branch: `release/2026-08-27` (detached, `261e31bdcbc`).
Companions: architecture `doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md`,
design `doc/05_design/compiler/plugin_arch/versioned_param_objects_and_interfaces.md`,
plan `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`.

Every repo claim is pinned to `file:line` as read on this branch. "Does not
exist" means a `/usr/bin/grep -rn` over `src/`, `scripts/`, `doc/` (vendor
excluded) returned zero hits.

## 1. MDSOC / MDSOC+ as the repo defines them

- MDSOC = layered composition model over the numbered layers `00.common` ..
  `99.loader`, with `85.mdsoc` as its own layer
  (`doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md:24-42`).
  Visibility law: tree-private by default; parent-public / next-layer-public /
  common-node-public; sibling-to-sibling forbidden (`:123-130`, `:279-297`).
- Dimensions are real code: feature dimension `src/compiler/85.mdsoc/feature/`
  (13 concerns), construct dimension `src/compiler/85.mdsoc/construct_types/`
  (`construct_capsule.spl`, `shared_binding.spl`, `cross_dimension_query.spl`),
  weaving `85.mdsoc/weaving/{join_point,advice_form,weaving_rule}.spl`
  (`mdsoc_architecture_tobe.md:147-155`).
- MDSOC+ = the ECS business-layer rule set adopted 2026-04-17
  (`mdsoc_architecture_tobe.md:360-459`). Rule table `:372-378`: **kernel
  (ring 0) and drivers are MDSOC-only, no ECS**; userland services/apps are
  "MDSOC capsule outside, ECS inside". ECS does not replace capsule boundaries,
  capability tokens or ports (`:404-410`). Dynamic runtime component
  registration is explicitly out of scope (`:444-448`). Stdlib target
  `src/lib/{nogc_sync_mut,gc_async_mut}/ecs/` (`:391-393`): `gc_async_mut/ecs/`
  has all six files; `nogc_sync_mut/ecs/` has only `change_detection.spl`, so
  acceptance criterion 1 (`:414`) is not met.
- A second, unrelated "MDSOC+" exists:
  `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
  (status "Proposed architecture" `:9`; six-layer tagged structural compute).
  Not used here.
- Kernel-vs-pluggable: **no compiler/runtime definition exists.** "pluggable"
  appears once in `doc/04_architecture/compiler/**`
  (`mdsoc_plus_tagged_structural_compute_architecture.md:2380`, placement
  policy) and zero times in `src/compiler/**/*.spl`. The nearest contract is the
  frozen extension-identity tuple in
  `doc/04_architecture/compiler/extension_completeness.md:29-36`
  (`owner_enum + constructor + provider_module + local_ordinal +
  payload_schema_hash + module_abi_hash + schema_abi_version`) and the
  privileged-host-import admission policy
  (`doc/04_architecture/compiler/privileged_host_import_admission.md:1-30`,
  PROPOSED/RED, owner `src/compiler/35.semantics/privileged_host_imports.spl`).

## 2. Existing plugin-like machinery (aspect dynload lane)

| Term | Meaning | State |
|---|---|---|
| capsule | composed unit keyed by (dimension, canonical_path) | implemented: `src/compiler/85.mdsoc/types/virtual_capsule.spl:10-37`, `types/capsule_{rules,visibility,export}.spl` |
| facet | external witness (impl name + owning aspect + generation) | text-keyed registry implemented: `src/lib/common/facet_registry.spl:57-230` (`catalog_bind_facet`, `try_facet`, `facet_absence`, `facet_witness_impl`, `facet_witness_generation`); declaration parsing `src/compiler/35.semantics/aspect_seal/facet_model.spl:366-423`. Typed `facet<T>` **not implemented** (`doc/04_architecture/compiler/aspect_dynload/typed_facet_witness_transaction_2026-08-26_tldr.md:3`) |
| aspect pack (APK) | signed SMF-embedded pack of facet/joinpoint/startup entries | most complete piece: `src/lib/common/aspect_pack.spl` (`APK_MAGIC_V1`, `APK_SCHEMA_V1 = 1`, activation modes `APK_ACT_{OFF,STATIC,STARTUP,LAZY_FACET,MANUAL,LAZY_PATCHABLE,HOT}`, facet states `APK_FC_{BOUND,QUIESCING,UNLOADED}` `:65-119`; `Apk*V1..V3` records `:123-334`; loader `apk_loader_new :1753`, `apk_loader_register_pack :1887`, `apk_try_facet :1994` (resident-only), `apk_load_facet :2008`, `apk_load_aspect_manual :2024`, `apk_unload_facet_v1 :2477`; content hash/signature `:2543-2592`; ed25519 `:2607-2623`); compiler side `src/compiler/99.loader/aspect_pack_{io,section,index_cache}.spl` |
| facet acquisition gate | ordered checks | `aspect_pack.spl:2125-2205`: quiescing refusal, activation policy (`APK_ASPECT_EXCLUDED`/`MANUAL`), `APK_PACK_MISSING`, `APK_ROUTE_DANGLING`, **contract ABI hash equality `APK_ABI_MISMATCH`**, then opt-in `required_core_public_abi_hash`, `required_core_layout_hash`, `variant_fingerprint` set by `apk_loader_set_expected_core_abi/_variant_fingerprint/_core_layout` (`:1796-1808`), skipped when unset (`:2196-2205`). Sealed state forbids lazy I/O `E-APACK008` (`:2120-2122`, `:1773`) |
| patchpoint | per-call-site patchable advice slot | **not implemented** (`doc/04_architecture/compiler/aspect_dynload/patchpoint_and_signing_prerequisites_2026-08-19.md:26-30`); only whole-symbol RW->RX relocation (`module_loader.spl:400-421`) |
| binding plan | `FacetBindingPlan` / `binding_plan_id` | **design-only, undefined** (`binding_plan_id_resolution_2026-08-19.md:9-40`) |
| registry transaction | `AspectRuntimeRegistry` | designed only (`registry_transaction_2026-08-22_tldr.md:3-18`); no such type in `src/` |
| facet_abi | `src/lib/common/facet_abi.spl`, `FACET_ABI_VERSION_V1` | **does not exist**; named as to-be-created in `doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md:324-327`; pre-referenced by `src/app/compiler_schema/{codec_gen.spl:52,70, visitor_gen.spl:68, fold_gen.spl:56,70}` |
| compile-time "plugin" | `optimizer_plugin_registry_*` | in-process descriptors, no loading: `src/compiler/60.mir_opt/optimizer_plugin.spl:267-319` |

## 3. Dyn/static link switching: what exists

Premise correction: a unified link-mode switch **does not exist** (0 hits for
`--link-mode`, `link_mode`, `LinkMode`, `SIMPLE_LINK_MODE`, `rt_dlopen`,
`load_plugin`, `libsimple_runtime.so`). Three partial mechanisms exist:

1. `--emit-shared` (exclusive with `--emit-object`/`--emit-archive`), parsed
   `src/app/io/_CliCompile/compile_targets.spl:668`, validated `:846`, passed
   to the driver only as `env_set("SIMPLE_NATIVE_BUILD_EMIT_OBJECT","shared")`
   `:911-912`; read `src/compiler/80.driver/driver_aot_native_output.spl:731-734`,
   acted on `:1078-1087`; API `aot_shared_library`
   `src/compiler/80.driver/driver_public_shared.spl:35,93`;
   `BackendKind.SharedLib` `src/compiler/10.frontend/core/backend_types.spl:55`,
   `70.backend/linker/link.spl:56`. Seed: `NativeBinaryOptions.shared`
   `src/compiler_rust/compiler/src/linker/native_binary_options.rs:95-96`,
   default `false` `:122`; consumed `linker/native_binary/linker.rs:235,262,288-300`.
2. APK activation modes (`aspect_pack.spl:65-119`) — `APK_ACT_STATIC` vs
   `STARTUP`/`LAZY_FACET`/`HOT`: per-plugin binding time, same catalog check.
3. Bootstrap modes `dynload` (default: native exe + SMF cache artifacts) vs
   `one-binary` (`doc/04_architecture/compiler/bootstrap_build_modes.md:11-15`).

Default link is static: `libsimple_runtime.a` found by directory probe
(`linker/native_binary/linker.rs:147,161`); rationale in
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:570-575`
(incomplete `.so` export list; avoid rpath into build tree); Stage4 forbids
aggregate archives as providers (`70.backend/backend/stage4_symbol_closure.spl:782-785`).
Runtime dlopen: `src/runtime/runtime_dynload.c:67,462` (`RTLD_NOW|RTLD_LOCAL`),
entries `spl_dlopen{,_checked}` `:447,452`, `spl_dlsym{,_checked}` `:469,474`,
`spl_dlsym_process_checked` `:491-503` — **no digest/signature/version check**.
Simple wrappers `src/lib/nogc_sync_mut/sffi/{dynamic,guest_dlopen,dynamic_versioned}.spl`;
`dynamic_versioned.spl`: `LibVersion :23`, `load_versioned :50`, soname
candidates `lib<name>.so.MAJ.MIN.PAT` `:170-187`, `MultiVersionLoader` cache
`:113-160`, `has_symbol :78`, `missing_symbols :94`; every loader
`@unsafe(reason: "loads an unverified versioned dynamic provider")` (`:49,64,68,116,142`).
Linker selection env: `SIMPLE_LINKER` (`70.backend/linker/mold.spl:95-118,667`),
`SIMPLE_LINKER_FLAVOR` (`_LinkerWrapper/native_linking.spl:748-750`),
`SIMPLE_LINKER_SCRIPT` (`backend/simpleos_native_linkers.spl:110`),
`SIMPLE_LINK_OBJECTS` (`backend/llvm_native_link_stage4_projection.spl:40-123`),
`SIMPLE_NATIVE_RUNTIME_BUNDLE` (`backend/llvm_native_link_orchestrator.spl:119-121`).

## 4. Versioning / compatibility mechanisms — verdict table

Note: the task brief cited `cache/action_key.spl:197-204`; on this branch the
file is `src/compiler/80.driver/cache/action_key.spl` and `interface_digest_of`
is at `:250-255`.

| # | Mechanism | Where | What it versions / how computed | Wired? | Verdict |
|---|---|---|---|---|---|
| 1 | `interface_digest_of(parts)` textual v1 | `80.driver/cache/action_key.spl:250-255`; `source_interface_parts :267` (keeps `fn/pub fn/me/extern fn/struct/class/enum/trait/type/export/impl` lines; **struct field lines NOT captured**); `interface_digest_of_source :275`; `dependency_interface_fold :286` (`simple/dep-interfaces/v1`); `struct ActionDep{module_id, iface_digest} :31`, encoded `:198-200` | sha256 over `simple/interface/v1` canonical seq | **yes**: `driver_build/incremental.spl:14,388`, `watcher/smf_manifest.spl:18,358`, `sif/sif.spl:46,78,153,196`, `cache/block/block_key.spl:57`, `cache/integration/shadow_mode.spl:100`. The "zero call sites" note in `.claude/rules/commands.md` and `src/lib/scv/build_invalidation.spl:12,38,172` is stale. | **reuse for cache keys only**; unfit for ABI (blind to fields) |
| 2 | typed compile-interface digest | `35.semantics/interface/compile_interface.spl`: domain `simple/compile-interface/v1 :27`, `interface_digest_with_domain :39`, encoders fn/fields/struct/class/enum/trait `:48-102`, `compile_interface_digest :131` | typed surface incl. fields | consumers: `src/lib/scv/hir_fingerprint.spl:27-28,158`, `test/01_unit/compiler/interface_compat/compile_interface_spec.spl` | **improve** into the ABI digest (design §3) |
| 3 | `ModuleIdentity` | `35.semantics/interface/module_identity.spl:24-31` `{module, source_digest, implementation_digest, compile_interface_digest, abi_interface_digest, compile_semantic_digest, link_export_digest}`; header `:3` "Compute-and-log only: NOT wired"; `abi_interface_digest` = placeholder `simple/abi-interface/placeholder-v0` re-hash `:9-22` | placeholders | no | **replace** placeholders with `simple/abi-interface/v1` |
| 4 | SMF manifest | `80.driver/watcher/smf_manifest.spl`: `SmfManifestEntry :26` `{source_path, smf_path, source_hash: i64, compiled_at, backend, opt_level, release, debug_info, gc_off, profile, allowed_families, iface_digest :41}`; `SmfManifest{version, entries, updated_at} :43-46`; writer `version: 3 :54`; reader defaults to 1 on parse failure `:220,231-233`, never rejects; `source_hash = rt_hash_text`, 0 = fail-closed sentinel `:146-155`; `IfaceDigestVerdict`/`smf_manifest_entry_iface_verdict`/`smf_manifest_iface_diagnostic :163-188` print only; row check on interpret path `driver_api_interpret.spl:55` | per-artifact | partly | **improve**: gate `version`, make iface verdict a rejection, add `abi_digest` + `provides`/`requires` columns |
| 5 | cache protocol schema | `80.driver/cache/schema/cache_protocol.sdn:30-31` `version: 2 / supersedes_schema_version: 1`; `schema_version` KEY field of ActionKey `:181,218`, aspect/impl record `:499-502`; "rename is a schema_version bump" `:804-805` | spec doc | enforcement in code | reuse |
| 6 | block key | `80.driver/cache/block/block_key.spl:30-31` `{body_tokens_digest, dep_ifaces: [ActionDep]}` | per-block | yes | reuse |
| 7 | producer identity | `80.driver/driver_build/incremental.spl:250-252` `exe=;compiler=;runtime=;bundle=`; `native_build_compiler_identity :254-262`; executable hash `:181`; frontend identity `:266`; lane `SIMPLE_CACHE_SCOPE :274`; scope key `lane=;backend=;cpu=;features=;opt=;compiler= :292-301` | whole compiler | yes: `70.backend/build_native.spl:28,54`, `driver_aot_native_output.spl:34,219`, `driver_source_pipeline_parsing.spl:17,242`, `10.frontend/frontend_parse_cache.spl:26` | reuse; this is the coarse gate that makes any kernel change invalidate everything, which is correct for K0 |
| 8 | `src/lib/simple.sdn` | `project: name: simple-std, version: 1.0.0-rc.1, type: library, dependencies: [- project: ../../compiler_rust]`; readers `80.driver/project.spl`, `00.common/config.spl`, `00.common/assurance/package_pins.spl`+`policy.spl` (only semver-ish checks), `70.backend/linker/link_deps.spl`, `99.loader/module_resolver/resolution.spl`, `src/app/info/main.spl:116` | package | version never compared | **improve**: add `provides:`/`requires:` (design §6) |
| 9 | APK record suffixes + ABI hash gate | `aspect_pack.spl:123-334`, `:2125-2205` | pack records, facet contracts | yes, opt-in core gates | **improve**: make core gates mandatory; align param-object versioning with this convention |
| 10 | extension identity tuple | `doc/04_architecture/compiler/extension_completeness.md:29-36`; `dense_tag_map.spl`, `completeness_seal/{manifest,required_interfaces}.spl` | extension payloads | frozen | reuse as the record-versioning convention |
| 11 | `dynamic_versioned.spl` | `:23-187` | soname filename only | yes | **replace** matching with digest negotiation |
| 12 | lib-local ABI gates | `nogc_sync_mut/mcdc/dynamic_aspect.spl:140-143` (`MCDC_ASPECT_ABI_V1`/`SCHEMA_V1` rejection); `spec/evidence/counterpart/provider_registry.spl:17,103`, `package_registry.spl:31,282-300`, `sffi/counterpart_abi.spl:63`; `composition/sci_generator.spl:12` + `sci_reader.spl:129` (`schema_version u16 = 1`); `mission_critical/*_v1.spl` | per-lib | yes | reuse as precedents; unify under one negotiation record |
| 13 | runtime.h | per-struct `RT_OWNED_PROCESS_RECEIPT_VERSION 1 :822`, `..._CANCEL_RECEIPT_VERSION 1 :845`, `..._ASYNC_VERSION 2 :859`, `..._OBSERVATION_VERSION 2 :915`; `rt_gpu_provider_abi_version() :359` | per-capsule | yes | reuse; **no global `SIMPLE_ABI_VERSION`/`RT_ABI_VERSION` exists** — add one K0 constant (design §3.4) |

Does not exist: ABI/layout digest of any kind; param-object field versioning;
version field inside `.smf` objects (only the sidecar); any compat gate that
rejects on `SmfManifest.version` or `cache_protocol.version`; semver comparison
outside package-pins.

## 5. Layer structure and seams (summary; detail in architecture doc §3)

`src/compiler/` `.spl` counts: `00.common` 97, `10.frontend` 166, `15.blocks` 28,
`20.hir` 66, `25.traits` 9, `30.types` 60, `35.semantics` 145, `40.mono` 28,
`50.mir` 95, `55.borrow` 10, `60.mir_opt` 88, `70.backend` 378, `80.driver` 143,
`85.mdsoc` 166, `90.tools` 247, `95.interp` 20, `99.loader` 66.

| Seam | Mechanism today | Adding one edits kernel? |
|---|---|---|
| backends | `enum BackendKind` `70.backend/backend/backend_types.spl:20-32`; `case` switches `backend_factory_full.spl:113-137`, `codegen_factory.spl:37-41`; parallel string switch `00.common/mir_target_context.spl:91-95`; `OptimizerBackendKind` `60.mir_opt/mir_opt/pattern/rule_engine.spl:41,106-118`; numeric ids `80.driver/cache/compile_options_hash.spl:239,251`; only interface-like seam `struct BackendPort` `70.backend/backend_port.spl:15-25` (struct of `any` fn fields; one implementor `85.mdsoc/feature/codegen/backends/interpreter/backend.spl:38-49`; held on `CompileContext.backend` `00.common/compiler_services.spl:147,217`) | yes, 7 files |
| runtime bundles | `SIMPLE_NATIVE_RUNTIME_BUNDLE` env string `driver_build/incremental.spl:260`; no `RuntimeBundle` type | n/a |
| SFFI providers | lint allowlist `scripts/check/no_direct_rt_allowlist.txt:5-11`; only registration API is the interpreter's `interp.register_extern` `src/app/interpreter/module/evaluator.spl:60`; unbacked externs return nil (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`) | no registry |
| lint rules | monolithic `Linter` class `90.tools/lint/_LintMain/lint_checks.spl:71,198,503,617,658` + sibling files; no rule trait/table | yes |
| MCP tools | `src/app/mcp/tool_table.spl:16-22` hand-built array; dispatch `main_dispatch.spl`, `main_static_tools.spl`, `main_lazy_*_tools.spl` | yes, 2 files |
| target triples | per-target constants `70.backend/target/riscv32.spl:47-121`; `enum Arch` `70.backend/linker/smf_enums.spl:62`; `src/lib/common/target/` and `parse_target_triple` **do not exist** | yes |
| interpreter | `src/compiler/95.interp/` (tiered JIT string switch `execution/tiered_jit.spl:272-274`), `10.frontend/core/interpreter/`; Rust seed bootstrap-only (`bootstrap_build_modes.md:52-55`) | — |
| bootstrap chain | `bootstrap_compiler_backend_stage_split.md:9-14,22`; stage2/3 compile `src/app/cli/bootstrap_main.spl` (`scripts/bootstrap/bootstrap-from-scratch.sh:2085,2169,2212,2244`), release lane compiles `src/app/cli/main.spl` (`:1338`); backend selectable, **default `llvm`, `cranelift` also supported** (`bootstrap-from-scratch.sh:112,1482`; `bootstrap_main.spl:229-237,273-277`); the driver-side minimal entries `80.driver/bootstrap_main_minimal.spl:9`, `bootstrap_types_main.spl:8` hardcode `BackendKind.Cranelift` but are not used by the script; `--entry-closure` "a reducer, not an authority" (`bootstrap_build_modes.md:26`); no minimal core-set file list exists | — |

## 7. Aspect injection today (logging, coverage/MCDC, lint, assurance)

- Coverage/MCDC is injected by **source rewriting**:
  `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:792-869`
  `build_coverage_wrapper` (twin `src/app/test_runner_new/test_executor_parsing.spl:316`)
  writes `$TMP/simple_cov_<flattened>.spl` (`:804`) = preamble + original +
  epilogue as string literals (`:869`). Enabled by `options.coverage` or
  `SIMPLE_MCDC_MODE in {on,dynamic}` (`:793-796`). Preamble names
  `test_runner_prepare_mcdc_recording`, `mcdc_default_policy`,
  `mcdc_dynamic_probe_controller_load_builtin_current_owner`,
  `scenario_governance_mcdc_exclusions_reset`, and a sha256-verified
  `--simple-mcdc-manifest=` contract (`:826-834`); epilogue
  `rt_coverage_dump_sdn()` (`:845-857`) and
  `test_runner_produce_mcdc_evidence_v1` (`:859-867`).
- Compile-time weaving does run in the default pipeline:
  `src/compiler/80.driver/driver_pipeline_aop.spl` (advice from
  `hir_mod.aop_advices` `:47-51`; validation `:54-64`; conflict check `:97`;
  `weave_function` + `apply_weaving_result` per MIR function `:104-112`; early
  return when `not config.enabled` `:88`); called from
  `driver_pipeline_execution.spl:27`, `driver_orchestration.spl:306`,
  `driver_aot_pipeline.spl:121-123`, `driver_source_llvm_ir.spl:176`.
  `85.mdsoc/weaving/` supplies only the data types (`join_point.spl:7,14`,
  `advice_form.spl:4`, `weaving_rule.spl:6`).
- Aspect parameters are passed three different ways: **typed object**
  (`McdcPolicy`/`McdcMode` into `McdcDynamicAspect.activate`,
  `src/lib/nogc_sync_mut/mcdc/dynamic_aspect.spl:128-163`, which also checks
  owner, monotonic barrier, quiescence, `abi_version == MCDC_ASPECT_ABI_V1`
  `:140`, schema, readiness; codes `MCDC-E-DYNAMIC-{BARRIER,NOT-QUIESCENT,ABI,SCHEMA,UNSUPPORTED,LOAD}`);
  **env strings** (`SIMPLE_AOP_LOG_CALLS`, `SIMPLE_AOP_LOG_ASSIGNMENTS`,
  `SIMPLE_AOP_COMPILE_LOG_LEVEL`, `SIMPLE_AOP_RUNTIME_LOG_LEVEL` parsed into
  `AopLogInstrumentationConfig` at `driver_pipeline_aop.spl:68-80`;
  `SIMPLE_AOP_DEBUG` `10.frontend/core/aop_debug_log.spl:53`); and
  **generated source text** (the coverage wrapper). This is the parameter-object
  problem in its rawest form: three encodings, none versioned.
- Streaming surfaces (`SIMPLE_STAGE4_STREAMING_SURFACES`) are **not an aspect**
  but a memory strategy: parse one physical file at a time and commit the module
  surface in place (`driver_source_pipeline_parsing.spl:377-556`
  `parse_all_streaming_surfaces_in_place_impl`; `driver_hir_pipeline_lowering.spl:103,395`;
  env read `driver_phase_gates.spl:59`; set by `bootstrap-from-scratch.sh:1346`;
  required by `scripts/check/check-bootstrap-portability.shs:138-139`; rationale
  `doc/08_tracking/bug/bootstrap_stage4_ast_hir_overlap_memory_2026-07-27.md:102,207,226`).
  No list-of-surfaces file exists; it is a boolean mode.

## 8. Startup path (what the plugin architecture must not slow down)

- Interpreter/CLI: no `SessionCache` symbol exists under
  `src/compiler/10.frontend/core/`; "Session setup" is a test-runner phase
  (`src/app/test_runner_new/test_runner_main.spl:392,606`,
  `test_runner_execute.spl:50`, `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:204`).
  Measured CLI end-to-end startup is ~50-60 ms
  (`doc/10_metrics/startup/startup_perf_check_2026-08-17.md:22`).
- `SIMPLE_NATIVE_INCREMENTAL` is Rust-seed only
  (`src/compiler_rust/driver/src/cli/native_build.rs:569`;
  `compiler/src/pipeline/native_project/mod.rs:1596-1605`, default off; receipt `:1171`).
- Loader: resident-only lookup `apk_try_facet`
  (`src/compiler/99.loader/module_loader_compat.spl:442`) vs loading path
  `_apk_load_facet_indexed_v1` (`:560`). Lazy I/O is refused once operational
  state is sealed (`aspect_pack.spl:1773,2120-2122`).
- MCP "lazy" tools are separately compiled tool-group entrypoints
  (`src/app/mcp/main_lazy_*.spl`, 11 files, via `main_lazy_json.mcp_run_argv`
  `main_lazy_query_tools.spl:19`) — process-level laziness, not deferred init.

## 9. Bootstrap closure and receipts

- Driver `scripts/bootstrap/bootstrap-from-scratch.sh`; receipts
  `--bootstrap-receipt=<path>` / `SIMPLE_BOOTSTRAP_REASON_RECEIPT` /
  `--validate-bootstrap-receipt` (`:114-135,220-241,408`), produced by
  `produce-bootstrap-planner-admission-v2.shs` and
  `src/app/build/bootstrap_receipt_planner.spl` (`bootstrap_receipt_main.spl:7-8`).
- `CompilerArtifactManifestV1` appears only in
  `scripts/bootstrap/stage4-tooling-matrix.shs` and `stage4-tools-only.sh`;
  **no `.spl` definition exists**.
- Rebuild gate `bootstrap_wide_inputs_hash()` (`bootstrap-from-scratch.sh:1018-1028`)
  hashes platform+backend+mode, seed fingerprint, every `src/compiler/**/*.spl`,
  and `SIMPLE_*` env matching `(AOP|MDSOC|WEAV|LOAD|INTERPRET|EXECUTION|LIB|NATIVE_BUILD)`;
  `prepare_native_cache()` (`:1091-1125`) clears on clean-release, one-binary,
  `--fresh-cache`, or stamp mismatch. **`src/app` and `src/lib` are not in the
  hash.** This is the concrete "kernel rebuild" trigger the goal wants to
  narrow: today every `src/compiler` file is a kernel input.
- `--entry-closure` discovers the transitive module closure from `--entry`
  (`:1331-1338,2167-2169,2239-2244,2737-2741`; env
  `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0` `:2488`;
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:321`).
- No "plugins required for self-host" list exists.

## 10. Package / dependency model

- `src/lib/simple.sdn`: `project:` (name `simple-std`, version `1.0.0-rc.1`,
  type library, root/source_dir/test_dir), `dependencies: [- project: ../../compiler_rust]`,
  plus a `gpu:` block (`gpu_config.load_project_gpu_config`).
- Readers of `dependencies:`: only
  `src/compiler/00.common/assurance/package_pins.spl:343-356` (`DepEdge :121`,
  edge walk `:483`, transitive closure `:501`) and
  `src/compiler/70.backend/linker/link_deps.spl:3`. `project.spl`,
  `config.spl`, `assurance/policy.spl`, `module_resolver/resolution.spl`,
  `src/app/info/main.spl` do **not** read it.
- Other manifests: `src/compiler/simple.sdn`, `src/compiler/00.common/simple.sdn`,
  `src/app/simple.sdn`, `src/app/sffi_gen.templates/MANIFEST.sdn`,
  `test/fixtures/package_pins/*/simple.sdn`.
- Semver: `package_pins.spl` has **no range support** (exact pins + waivers).
  `^`/`~` only in `src/lib/nogc_sync_mut/package/semver_old.spl:257-267`
  (`satisfies`, `satisfies_caret`, `satisfies_tilde`), exported
  `package/__init__.spl:36-41`; its test is commented out
  (`integration_test.spl:75-163`).
- Lockfile `simple.lock`: `src/lib/nogc_sync_mut/package/lockfile.spl:14-322`
  (`lockfile_path :287-289`), also `gc_sync_mut/package/lockfile.spl`, `src/app/pkg/lock.spl`.
- Package manager `src/app/pkg/{main,install,lock,manifest,resolver,version}.spl`
  (`install|i` `main.spl:223`, `add|a` `:251`); legacy commands in
  `src/app/cli/command_registry.spl:86-89,142` (`update`, `lock` registered with
  empty handler paths); `src/app/pkg` is **not wired** into CLI dispatch.
- **A version-range resolver does not exist**: `src/app/pkg/resolver.spl`
  resolves locations (`git_clone_or_fetch :83`, `resolve_path_dep :148`,
  `resolve_dep :168`, `check_conflicts :200`, `resolve_all :218`); no
  backtracking or range intersection anywhere.

## 6. Prior art

Evidence level: **not fetched.** WebFetch/curl were hook-denied in this lane;
each item was verified on 2026-08-28 against search-engine snippets of the
primary page named in the Sources list (§6.1), and the mechanism descriptions
otherwise rest on model knowledge. Treat URLs as the authoritative pointer to
re-verify, not as quoted text.

| # | Mechanism | How the host avoids a rebuild | Cost / limit | Fit for Simple (no inheritance; traits/mixins/composition; `<>` generics; value+COW; SFFI to C) |
|---|---|---|---|---|
| 1 | Vulkan `sType`/`pNext` chains; `VkApplicationInfo.apiVersion`, `vkEnumerateInstanceVersion` (docs.vulkan.org/guide/latest/pnext_and_stype.html; docs.vulkan.org/refpages/latest/refpages/source/VkApplicationInfo.html) | existing layouts never change; new params are typed chain nodes skipped when unknown | global `sType` registry; runtime-only validation | good: an `ext: [ParamExt]` array of tagged value records is the COW-friendly equivalent of `pNext` |
| 2 | Win32 `cbSize` / `lStructSize` (`WNDCLASSEXW`, `OPENFILENAMEW`, `OPENFILENAME_NT4W`) (learn.microsoft.com/en-us/windows/win32/api/winuser/ns-winuser-wndclassexw; .../commdlg/ns-commdlg-openfilenamew) | callee honours caller's declared size; append-only | hand-maintained size->version map; wrong size = runtime error | simplest fit for `repr(C)` FFI param structs |
| 3 | COM `IUnknown::QueryInterface`, IIDs; "interfaces are immutable; new IID for any change" (learn.microsoft.com/en-us/windows/win32/com/queryinterface--navigating-in-an-object; .../rules-for-implementing-queryinterface) | old clients keep old vtables; new capability = sibling interface | IFoo2/IFoo3 proliferation | maps to `query(iface_id) -> Option<...>` on composed objects; interface id = `(name, major)` |
| 4 | Linux `EXPORT_SYMBOL` + `CONFIG_MODVERSIONS` prototype CRC in `Module.symvers`, `vermagic` (kernel.org/doc/html/latest/kbuild/modules.html) | unchanged prototypes keep old modules loadable; CRC mismatch => refuse | any prototype/layout change breaks all modules | directly reusable: prototype+layout digest checked at load = our `abi_digest` |
| 5 | ELF symbol versioning, version scripts, `.symver`; glibc (sourceware.org/binutils/docs/ld/VERSION.html; Drepper, How To Write Shared Libraries §3) | old impls kept under old version nodes | one default per symbol; ELF only | poor for PE/SimpleOS/baremetal; not the primary mechanism |
| 6 | LLVM `llvmGetPassPluginInfo` `{APIVersion, PluginName, PluginVersion, RegisterPassBuilderCallbacks}`, `LLVM_PLUGIN_API_VERSION` ("mismatch is an error"); C API "best effort" stability (llvm.org/doxygen/PassPlugin_8h_source.html; llvm.org/docs/DeveloperPolicy.html) | tiny versioned C handshake | one int gates all; plugins bind unstable C++ | trivial handshake; pair with #4/#10 |
| 7 | Swift library evolution: resilient structs, `@frozen` (github.com/apple/swift/blob/main/docs/LibraryEvolution.rst; swift.org/blog/library-evolution/) | clients never bake in offsets; fields added/reordered without ABI break | out-of-line accessors, runtime metadata; `@frozen` irreversible | natural with value semantics; `@frozen` ~ `repr(C)` K0 types |
| 8 | Java `ServiceLoader` `META-INF/services`; OSGi version ranges `[1.5,2)` consumers / `[1.5,1.6)` providers (docs.oracle.com/en/java/javase/17/docs/api/java.base/java/util/ServiceLoader.html; docs.osgi.org/whitepaper/semantic-versioning/060-importer-policy.html) | name discovery + range matching at resolve time | needs a resolver; no layout help | manifest discovery + provider-vs-consumer range asymmetry adopted in design §6 |
| 9 | .NET strong names + `<bindingRedirect>` (learn.microsoft.com/en-us/dotnet/framework/configure-apps/redirect-assembly-versions) | config rebinding without recompile | members must stay metadata-compatible | a `requires` override in `simple.sdn` plays the same role |
| 10 | Rust: no stable ABI, `#[repr(C)]`; `abi_stable` `#[sabi(kind(Prefix))]` prefix types, `StableAbi` layout compared at load (docs.rs/abi_stable/latest/abi_stable/docs/prefix_types/index.html; .../derive.StableAbi.html) | old host sees a prefix of the newer struct; digest-verified layouts | append-only; frozen alignment | closest match: prefix-append param objects + layout digest |
| 11 | GObject `GTypeInterface`, `g_type_interface_add_prerequisite` ("alternative to interface derivation"), `GLIB_VERSION_MIN_REQUIRED`, `glib_check_version()` (docs.gtk.org/gobject/concepts.html; docs.gtk.org/glib/compiling.html) | runtime vtable lookup; reserved padding | lookup cost; finite padding | prerequisites ~ trait bounds |
| 12 | Protobuf field numbers/unknown fields/`reserved`; FlatBuffers append-only + `deprecated` + `flatc --conform`; Cap'n Proto `@N` ordinals (protobuf.dev/programming-guides/proto3/; flatbuffers.dev/evolution/; capnproto.org/language.html) | wire identity is a number; readers tolerate unknowns | ordinal bookkeeping | ideal for COW value params crossing boundaries; `--conform` = our lint rule |
| 13 | SemVer (semver.org); Hyrum's law (hyrumslaw.com) | cheap range predicate | policy, not proof | governs which rules apply; digests answer Hyrum |
| 14 | libtool `current:revision:age` (gnu.org/software/libtool/manual/html_node/Updating-version-info.html) | pure additions keep `current-age` | interface set only | complements #5 for POSIX `.so` outputs |

Composite adopted (design doc): size/kind-prefixed value param records with
field ordinals and presence bits (#2, #10, #12) + `ext[]` typed extension chain
(#1) + interface identity `(name, major)` with query (#3, #11) + prototype/layout
digest checked at load (#4, #10) + one plugin API-version int (#6) + provider /
consumer version ranges (#8, #13).

### 6.1 Sources (primary pages; snippet-verified, not fetched — see §6 header)
- https://docs.vulkan.org/guide/latest/pnext_and_stype.html
- https://docs.vulkan.org/refpages/latest/refpages/source/VkApplicationInfo.html
- https://docs.vulkan.org/refpages/latest/refpages/source/vkEnumerateInstanceVersion.html
- https://learn.microsoft.com/en-us/windows/win32/api/winuser/ns-winuser-wndclassexw
- https://learn.microsoft.com/en-us/windows/win32/api/commdlg/ns-commdlg-openfilenamew
- https://learn.microsoft.com/en-us/windows/win32/api/commdlg/ns-commdlg-openfilename_nt4w
- https://learn.microsoft.com/en-us/windows/win32/com/queryinterface--navigating-in-an-object
- https://learn.microsoft.com/en-us/windows/win32/com/rules-for-implementing-queryinterface
- https://www.kernel.org/doc/html/latest/kbuild/modules.html
- https://sourceware.org/binutils/docs/ld/VERSION.html
- https://cs.dartmouth.edu/~sergey/cs258/ABI/UlrichDrepper-How-To-Write-Shared-Libraries.pdf
- https://llvm.org/doxygen/PassPlugin_8h_source.html
- https://llvm.org/doxygen/structllvm_1_1PassPluginLibraryInfo.html
- https://llvm.org/docs/DeveloperPolicy.html
- https://github.com/apple/swift/blob/main/docs/LibraryEvolution.rst
- https://www.swift.org/blog/library-evolution/
- https://docs.oracle.com/en/java/javase/17/docs/api/java.base/java/util/ServiceLoader.html
- https://docs.osgi.org/whitepaper/semantic-versioning/060-importer-policy.html
- https://learn.microsoft.com/en-us/dotnet/framework/configure-apps/redirect-assembly-versions
- https://learn.microsoft.com/en-us/dotnet/framework/configure-apps/file-schema/runtime/bindingredirect-element
- https://docs.rs/abi_stable/latest/abi_stable/docs/prefix_types/index.html
- https://docs.rs/abi_stable/latest/abi_stable/derive.StableAbi.html
- https://docs.gtk.org/gobject/concepts.html
- https://docs.gtk.org/gobject/type_func.TypeInterface.add_prerequisite.html
- https://docs.gtk.org/glib/compiling.html
- https://protobuf.dev/programming-guides/proto3/
- https://flatbuffers.dev/evolution/
- https://capnproto.org/language.html
- https://semver.org/
- https://www.hyrumslaw.com/
- https://www.gnu.org/software/libtool/manual/html_node/Updating-version-info.html
- https://www.gnu.org/software/libtool/manual/html_node/Libtool-versioning.html
