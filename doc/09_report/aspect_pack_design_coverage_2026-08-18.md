# Aspect-pack / dynload: design-to-implementation coverage (2026-08-18)

Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
Implementation under review: `src/lib/common/aspect_pack.spl`
Specs: `test/01_unit/lib/aspect_pack_spec.spl`, `test/01_unit/lib/aspect_pack_defect_class_spec.spl`

The design is a whole-language feature (grammar, placement IR, weaving, runtime
witnesses). `aspect_pack.spl` is deliberately only the **container + catalog +
routed loader** slice. Sections outside that slice are marked OUT-OF-SCOPE with
the reason; they are not claimed as implemented anywhere.

| § | Topic | Status | Evidence |
|---|---|---|---|
| 1-2 | Executive decision, motivation | N/A prose | — |
| 3 | Terminology | N/A prose | — |
| 4 | Research findings | N/A prose | — |
| 5.1-5.2 | Core independence, base layout stability | OUT-OF-SCOPE (compiler/codegen) | no code emitted by this module |
| 5.3 | Explicit optional API access | OUT-OF-SCOPE (frontend) | — |
| 5.4-5.5 | Binding completeness/uniqueness | PARTIAL | catalog-level uniqueness only: `apk_build_catalog_v2` rejects duplicate `(kind, key)`; `apk_build_pack_v2` rejects duplicate module ids. Type-level binding uniqueness is a compiler check. |
| 5.6 | ABI compatibility | IMPLEMENTED | `ApkModuleSourceV2.module_abi_hash` / `ApkCatalogEntryV2.abi_hash`; `_apk_acquire_facet` fails `APK_ABI_MISMATCH` |
| 5.7 | Atomic activation | PARTIAL | a failed bind is never published to the resident registry (`_apk_acquire_facet` publishes only on the success path); no generation/epoch object exists |
| 5.8 | Deterministic configuration | IMPLEMENTED | activation is a recorded catalog field, not runtime inference |
| 5.9 | No hidden runtime search | IMPLEMENTED | `apk_catalog_route_v1` / `_apk_acquire_facet`: exact key + exact pack path, no scan path in the module |
| 5.10 | Exact performance claims | IMPLEMENTED | loader counters `packs_opened` / `modules_decompressed` / `bytes_decompressed` / `cache_hits`, asserted in REQ-APK-DC-01, -08 |
| 6.1-6.6 | Grammar, facet decls, impls | OUT-OF-SCOPE (parser/HIR) | — |
| 6.7 | Facet acquisition API | IMPLEMENTED (loader analogue) | `apk_try_facet` (no I/O, resident only), `apk_load_facet` (policy-gated), `apk_load_aspect_manual` (`aspect.load`). `unload` MISSING — §14.7 states hot unload is not required initially. |
| 6.8-6.12 | Nominal static mode, mixins, advice eligibility | OUT-OF-SCOPE (frontend) | — |
| 7-8 | Ownership, source placement, root registry | OUT-OF-SCOPE (resolver) | — |
| 9.1-9.2 | Variant overlay, selection axes | OUT-OF-SCOPE (build config) | — |
| 9.3 | Aspect configuration | OUT-OF-SCOPE (config files) | — |
| 9.4 | Activation modes | IMPLEMENTED | `APK_ACT_OFF/STATIC/STARTUP/LAZY_FACET/MANUAL/LAZY_PATCHABLE/HOT`; enforcement in `_apk_acquire_facet` (`APK_ASPECT_EXCLUDED`, `APK_ASPECT_MANUAL`); `apk_activate_startup` binds the startup set. REQ-APK-06, REQ-APK-DC-07 |
| 9.5 | Cache-key separation | OUT-OF-SCOPE (driver cache) | fingerprints are computed by the build driver, not the container |
| 9.6 | Multi-profile deployments | MISSING (deliberate) | needs a `ProfileRecord[]` array and a profile-selected catalog; no consumer exists yet, so implementing it now would be speculative format |
| 10 | Deployment layout | OUT-OF-SCOPE (packaging) | packs are addressed by catalog-relative path (`apk_loader_register_pack`) |
| 11.1 | Level 1 Aspect Catalog | PARTIAL | FacetRoute (`apk_catalog_route_v1`), JoinpointRoute (`apk_catalog_route_joinpoint_v1`), StartupAspect (`apk_catalog_startup_keys_v1`) implemented as one kind-discriminated record array; `activation_mode` + `facet_contract_abi_hash` carried. **PackRef is MISSING** (`content_hash`, `index_hash`, `signature_policy`, `required_runtime_abi`) — signature/trust policy has no verifier in-tree, so a hash field with no checker would be decoration. `ProfileRecord[]` missing per §9.6. |
| 11.2 | Level 2 pack directory | PARTIAL | ModuleEntry: `module_id`, `aspect_id`, `module_abi_hash`, `required_core_public_abi_hash`, `variant_fingerprint`, chunk offset/size/crc — all uncompressed. `AspectEntry`, `BindingSummaryEntry`, `DependencyEntry`, `SignatureTable` MISSING (a module is one chunk here, so chunk_range/dependency ranges have nothing to range over; see §12). |
| 11.3 | Full metadata inside chunks | IMPLEMENTED by construction | only routing/compat data is duplicated uncompressed; payload bytes are opaque |
| 12 | Backward-compatible pack SMF | IMPLEMENTED | `apk_build_pack_v2` embeds complete module blobs; `apk_load_module_v1` returns the blob bytes for the existing SMF reader |
| 12.1 | SMF header compatibility | PARTIAL | `APK_FLAG_ASPECT_PACK` is set and an unflagged file is REJECTED (`APK_NOT_ASPECT_PACK`, REQ-APK-DC-04). UPDATED 2026-08-19: `SectionType.AspectPackDirectory` IS now a registered SMF section type (wire byte 16, `.aspect_pack`) in `src/compiler/70.backend/linker/smf_writer.spl` and in the authoritative Rust enum `src/compiler_rust/common/src/smf/section.rs`; `SMF_FLAG_ASPECT_PACK` (0x20) is defined in `smf_header.spl`, stamped by the writer whenever the section is present, and parsed into `SmfFlags.aspect_pack`. `AspectPackSignature`/`AspectPackDictionary` are still NOT registered: no signature verifier and no shared dictionary codec exist in-tree. |
| 12.2 | Compression policy | PARTIAL | directory + catalog uncompressed, one independent deflate frame per module, per-frame crc and declared uncompressed size — all present. Co-load clusters, page-aligned uncompressed hot chunks, split cold debug chunks and a pack-level zstd dictionary are MISSING (all explicitly optional in the design). |
| 12.3 | Whole-pack stream forbidden | IMPLEMENTED + MEASURED | REQ-APK-DC-01: `bytes_decompressed` equals exactly the selected frame; REQ-APK-DC-05: corrupting an unselected frame leaves other modules loadable |
| 13.1-13.2 | Hard/soft grouping constraints | OUT-OF-SCOPE (packer policy) | this module consumes a grouping decision, it does not make one |
| 13.3 | Independent loading mandatory | IMPLEMENTED | `apk_load_module_v1` loads exactly one module by id |
| 13.4 | Repacking does not recompile | IMPLEMENTED by construction | the builder takes opaque module payloads |
| 14.1 AspectCatalogReader | | IMPLEMENTED | `apk_open_catalog_v1` + route fns |
| 14.1 AspectPackProvider | | IMPLEMENTED | `apk_open_pack_v1` + `apk_load_module_v1` by `(pack_path, module_id)` |
| 14.1 AspectPackIndexCache | | MISSING | needs a real mmap/file layer; this module works on byte arrays, so caching a directory mapping has nothing to map. Tied to §15. |
| 14.1 FacetBindingRegistry | | PARTIAL | a facet-key -> loaded-module registry exists (`apk_try_facet`, `from_cache`, `cache_hits`); the `(concrete_type_id, facet_interface_id, generation) -> witness` map is runtime/codegen work |
| 14.1 AdviceBindingRegistry | | MISSING (out of scope) | needs join-point slots and patchpoints in the backend; only the catalog ROUTE to a slot exists here |
| 14.1 AspectActivationManager | | PARTIAL | `_apk_acquire_facet` runs route -> policy -> load -> ABI-check -> publish; no explicit state-machine object |
| 14.2 | Runtime state machine | MISSING (out of scope) | states beyond Catalogued/ChunksLoaded/Bound need the runtime loader |
| 14.3 | First `facet<T>()` operation | IMPLEMENTED for steps 3-5 | resident-registry check, FacetRoute consult, policy gate, exact pack open, one frame inflate, ABI validation, publish. Steps 1-2 (type id, inline cache) and 6-7 (sidecar state, `FacetRef`) are runtime/codegen. |
| 14.4 | Open-world interface bindings | OUT-OF-SCOPE (runtime type registry) | — |
| 14.5 | Stateless/per-type/per-object state | OUT-OF-SCOPE (runtime) | — |
| 14.6 | Concurrency | PARTIAL | duplicate work is avoided by the resident registry; there is no activation future/dependency-cycle stack (this module has no concurrency primitives) |
| 14.7 | Unload | MISSING, by design | "Hot unload is not required for the initial release." |
| 15 | Mapping and I/O policy | MISSING (out of scope here) | the module is byte-array based; `pread`/`WILLNEED`/partial mapping belong to the loader's file layer |
| 16 | Facet contracts and SHB metadata | OUT-OF-SCOPE | — |
| 17 | ABI and compatibility model | PARTIAL | `facet_contract_abi_hash` is enforced; `required_core_public_abi_hash` and `variant_fingerprint` are CARRIED and readable but not compared (nothing in-tree publishes a core ABI hash to compare against — comparing against an invented value would be a fake gate) |
| 18 | Access and mutation policy | OUT-OF-SCOPE (frontend attributes) | — |
| 19 | Mission-critical profile | OUT-OF-SCOPE (build policy) | — |
| 20 | Exact performance contract | PARTIAL, the container half MEASURED | §20.3/20.4 first-use and steady-state claims are asserted by counters (REQ-APK-DC-01, REQ-APK-DC-08). §20.1/20.2 startup and hot-path costs need generated code to measure. |
| 21 | Diagnostics | PARTIAL | pack/load diagnostics are explicit typed codes (`APK_*`, 14 of them); compile/type and source/path diagnostics are frontend work |
| 22 | Compiler and IR architecture | OUT-OF-SCOPE | — |
| 23 | Integration with existing architecture | PARTIAL (2026-08-19) | `src/compiler/99.loader/aspect_pack_section.spl` finds the `.aspect_pack` section in a parsed `SmfReaderMemory` and registers its payload with the aspect-pack provider; `ModuleLoader.load` calls it and exposes `aspect_facet`/`resident_aspect_facet`. Spec: `test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl`. The three `ModuleLoader`-driven examples are RED on a pre-existing interpreter defect — `doc/08_tracking/bug/module_loader_load_unrunnable_jit_method_not_found_2026-08-19.md` |
| 24 | Development plan | Phase 4 (aspect pack v1) and the catalog half of Phase 5 are the parts this file covers | — |
| 25.3 | Pack behaviour tests | IMPLEMENTED | REQ-APK-01..07, REQ-APK-DC-01..09 |
| 26-30 | Example, rejected alternatives, references | N/A prose | — |

## Changes made in this pass

`src/lib/common/aspect_pack.spl`:
- §9.4 activation modes as catalog data + enforcement (`APK_ASPECT_EXCLUDED`,
  `APK_ASPECT_MANUAL`), `apk_load_aspect_manual`, `apk_activate_startup`.
- §6.7 `apk_try_facet` — never performs I/O; resident-facet registry so a
  repeat acquisition reopens nothing (§14.3 step 3), with a `cache_hits` counter.
- §11.1 JoinpointRoute and StartupAspect records (`entry_kind`), so a facet key
  and a join-point slot key cannot satisfy each other.
- §11.2/§17 ABI identity in the pack directory (`module_abi_hash`,
  `required_core_public_abi_hash`, `variant_fingerprint`) and the
  `APK_ABI_MISMATCH` fail-closed check on the routed load path.
- `apk_build_pack_v2` / `apk_build_catalog_v2`; the v1 builders remain as
  thin defaulting wrappers.

## Deliberately NOT implemented

- PackRef `content_hash`/`index_hash`/`signature_policy` (§11.1) — no verifier
  or signing authority exists in-tree; an unchecked hash field is decoration.
- Multi-profile catalogs (§9.6), zstd dictionaries and co-load clusters (§12.2),
  AspectPackIndexCache and the partial-mapping I/O policy (§14.1, §15) — all
  require a file/mapping layer this byte-array module does not have.
- Unload (§14.7) — the design states it is not required initially.
- `required_core_public_abi_hash` COMPARISON (§17) — carried but not compared,
  because nothing in-tree publishes a core public ABI hash to compare with.
