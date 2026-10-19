# MIR shard export summaries (Go-style export data for MIR workers)

Status: **stage 1 landed behind `SIMPLE_MIR_SHARD_EXPORT_SUMMARIES=1`**. The summary
format, writer, loader and admission exist. Workers still lower from the full post-mono
HIR. Stage 2, summary-only lowering, is designed below but **not wired**. Source
research: `doc/01_research/compiler/compile_speed/go_and_others_compile_pipeline_2026-10-19.md`,
technique (a) (PR #3815).

## Problem

Every MIR shard worker (`SIMPLE_MIR_SHARDING=1`,
`src/compiler/80.driver/driver_build/native_mir_shard.spl`) re-runs the whole front half:
HIR for all ~1300 modules (from cache), typecheck, and whole-program mono. Only then does
it lower its ~1/K slice. The result:

- each worker needs about 16 GB (`SIMPLE_MIR_SHARD_WORKER_KB` default 16000000);
- only about 5 workers fit on the 83 GB host;
- cold MIR takes hours.

The target is 25+ workers at about 3 GB each, which gives cold MIR in under 10 minutes on
80 cores. That requires a worker to hold only its claimed modules' bodies plus a body-free
view of everything else.

## What MIR lowering of module M reads from other modules

Lines are against `origin/release_phase3` at branch point. Paths are under
`src/compiler/50.mir/` unless stated. In the direct lane one `MirLowering` instance lowers
every module, so state written while lowering one module is visible when lowering the next.
The direct lane is `lower_to_mir_with_target_context`
(`80.driver/driver_pipeline_lowering.spl:651`). M sees cross-module data through three
channels:

- (a) the `providers` argument, which is all of `ctx.mir_feed_modules`;
- (b) whole-closure prescans that run before the first module lowers;
- (c) process-global registries.

| # | Category | Site | Reads / keyed by |
|---|---|---|---|
| 1 | Provider HIR (all of it) | `_MirLowering/module_lowering.spl:2222` `lower_module(…, providers)`; driver `driver_pipeline_lowering.spl:1195` | every provider `HirModule`'s structs, classes, enums, impls, functions, constants, traits |
| 2 | Struct-name prescan | `module_lowering.spl:1637` `prescan_module_struct_names`; driver `:1062-1078` | field order and types of every module; first module wins on a bare-name clash |
| 3 | Layout rows | `module_lowering.spl:1688-1704` `struct_field_order`, `struct_field_hir_type`, `struct_bare_layout_owner` | keyed by bare name and `owner::Name` |
| 4 | Layout identity | `module_lowering.spl:672,684` `struct_identity_layout_key` | maps `owner::Name` to its layout key |
| 5 | Layout digests | `module_lowering.spl:720-743` `composite_layout_digests`, `composite_layout_owner_counts` | `compute_struct_layout` size, align and offsets |
| 6 | Foreign layout trace | `module_lowering.spl:745-791` `record_external_layout_reference` | the foreign layout digests M used |
| 7 | Composite inventory / defaults | `module_lowering.spl:1110` `register_module_composite_inventory_v1`; driver `:1107` | `class_type_names`, `struct_field_has_default`, `struct_field_default_expr` (**foreign `HirExpr`**) |
| 8 | Provider struct / class | `_MirLowering/provider_metadata.spl:639,585` | field types and defaults relocated into M's symbol table |
| 9 | Symbol relocation | `provider_metadata.spl:292,383,449` | defines symbols in M's table using `lookup_qualified_{type,function}_raw` |
| 10 | Enum variants / runtime id | `module_lowering.spl:945,862,1054,1076,1217`; driver `:1099` | indices, discriminants, payload shapes, owners; runtime id = hash(`runtime_name`) |
| 11 | Callable linkage | `provider_metadata.spl:87-97,143-163,179`; `function_lowering.spl:428` | mangled/link name = owner + display name; `callable_link_names` keyed `{module}#{member}` |
| 12 | Callee return / param types | `module_lowering.spl:1778-1970` -> `mir_data.spl:928-1163` `bootstrap_fn_ret_*` | **process-global**, keyed by function and call name |
| 13 | Callee parameter defaults | `mir_data.spl:1225`, `module_lowering.spl:1926`, `_MirLoweringExpr/switch_operators_calls.spl:1256` | foreign default `HirParam`s, by name and owner |
| 14 | Default providers / globals | `mir_data.spl:1206`, `_MirLowering/resident_default_global_owner.spl:13` | **process-global** owner symbol table and constants |
| 15 | Methods / extensions | `provider_metadata.spl:243,65,209`; `module_lowering.spl:2401` | `struct_method_syms`, `struct_method_return_*`, keyed `{class}::{method}` |
| 16 | Trait implementors / devirt | `provider_metadata.spl:702-768`; `method_calls_literals.spl:4982-5006` | `trait_impl_owners`/`methods`; needs `trait_impl_closure_complete` |
| 17 | Vtable shapes | `native_trait_registration.spl:163,209` | `native_trait_layouts` (sorted slots and signatures), implementations |
| 18 | Imported globals / statics | `provider_globals.spl:12,119-264`; `global_initializer_guard.spl:12` | provider constants and init wrappers, keyed `owner::name` |
| 19 | Imported externs | `exact_extern_provenance.spl:47` | provider extern declarations, keyed `{module}#{name}` |
| 20 | Mono instance placement | `40.mono/monomorphize_integration.spl:404-441,1007` | each specialization is inserted into its template owner's HIR (and every alias); ids start at `MONO_SYMBOL_BASE` |
| 21 | Archive-lane specialization schedule | `80.driver/cache/hir_mir_archive_consumer_v1.spl:291,332` | secondary emission selected by symbol, name and complete digest (no duplicate symbol) |
| 22 | Order-dependent counters | `module_lowering.spl:832` `canonical_type_symbols`; `mir_lowering_types.spl:116` `mcdc_next_runtime_id` | **values depend on lowering order** |
| 23 | Parse-time globals | `mir_lowering_stmts.spl:25` (resource registry), `:2623` (HAL flag) | process-global flags, set at parse time |
| 24 | Typed storage registry | `80.driver/driver_types.spl:898,939` | **not read by lowering.** It is filled during lowering and frozen at codegen (`driver_aot_pipeline.spl:394,463`). A worker's frozen identity already covers only the modules it lowered, so the registry needs no export row. Its identity is preserved because nothing changes it. |

The repo already has a body-free per-module carrier for rows 1-19:
`MirHirModuleDeclarationsV1` / `MirHirDeclarationRepositoryV1`
(`hir_declaration_types_v1.spl:146,166`). It holds the symbol table, function signatures
with `complete_function_digest`, nominal fields with `layout_digest`, enums and variants,
traits (methods and defaults), impls, bitfields and globals. Defaults and initializers are
stored as references to owned artifacts. `MirLowering` already lowers against that carrier
when `declaration_repository` is set: `_MirLowering/declaration_providers_v1.spl:77-465`
(`prescan_module_declarations_v1`, `register_declaration_provider_{globals,layouts,traits}`)
and `declaration_enum_metadata_v1.spl:84-140`. That route is the full0 archive lane,
`lower_archived_to_mir_v1` (`driver_pipeline_lowering.spl:526`). Its declarations are
in-process only: they are projected from the final mono repository, whose admission pins
are private to the driver process (`cache/hir_mono_final_repository_v1.spl:34-41`). The
codec was write-only (`hir_declaration_codec_v1.spl`, digest use only).

## Design

Reuse the declaration carrier as the export record. Do not invent a new format.

1. **Summary step (one process).** The coordinator (`run_mir_shards`,
   `src/app/cli/native_build_main.spl`) spawns one ordinary worker with
   `SIMPLE_MIR_SHARD_EXPORT_WRITE=<ledger>.export` before the MIR workers.
   `aot_compile` sees the variable after mono and calls `driver_mir_shard_export_write_v1`
   (`80.driver/driver_mir_shard_export_v1.spl`). For every source module with HIR, that
   function does the following inside its own transient scratch scope:
   - project with `mir_hir_project_module_in_owned_scope_v1`;
     - authority = `sha256("mir-shard-export-authority-v1\n" + native_sources_fingerprint)`;
     - key = `sha256(authority + module)`;
     - body digest = `sha256(hir_module_encode(module))`;
   - write the record;
   - promote only the digest text.

   The manifest is written last. The process exits without lowering.
2. **Record** `<dir>/<sha256(module)>.mirexport`. The payload uses the existing writer
   `mir_hir_write_module_declarations_v1`. The header has five lines: format
   `simple/mir-shard-export/v1`, build identity, module, declaration digest
   (`mir_hir_module_declaration_digest_v1`), and the payload sha256.
3. **Manifest** `<dir>/manifest`. It holds the format, the identity, the count, and one
   `module\tdigest` row per module in source order, followed by `seal <sha256(all
   preceding lines)>`. Its presence is the completeness seal. The coordinator deletes any
   old manifest before the step runs.
4. **Decoder** `50.mir/hir_declaration_decoder_v1.spl`. It is the field-for-field inverse
   of the writer and uses the generated `hc_dec_*` HIR readers.
   `mir_hir_decode_module_declarations_v1` accepts a record only if all of these hold:
   - the reader consumed the whole blob;
   - the decoded value **re-encodes to identical bytes**;
   - the digest equals the recorded one.
5. **Worker admission** (`driver_mir_shard_export_admit_v1`, called in
   `aot_compile_mir_shard_v1`). The manifest must be sealed and carry this identity, it
   must cover every source module with HIR, and every record must load and prove. All of
   this runs in a scratch scope and only the verdict survives. A refusal prints `fallback=full-hir`.
6. **Fail closed.** Every failure falls back to today's full load, never to partial
   information. The failures include: no bundle, summary process failure, stale or foreign
   identity, checksum mismatch, a byte-unequal re-encode, and a missing module.
7. **Bounded memory.** Nothing is cached. No new promoted root is created, and existing
   promoted roots keep their lifetimes. Producer and admission work one module at a time
   in scratch scopes.

### Stage 2 (not wired): summary-only lowering

To reach the target RSS, an admitted worker must, in order:

- (i) claim its modules **before** the front half (today claims happen inside
  `lower_to_mir`, `driver_pipeline_lowering.spl:1131-1166`);
- (ii) load only those modules' **post-mono** HIR, persisted by the summary step through
  `hir_cache_store`;
- (iii) install the admitted repository as `MirLowering.declaration_repository`;
- (iv) prescan declarations instead of `prescan_module_struct_names` and the inventory
  registrations;
- (v) lower its claimed modules through the archive-style per-module route.

Each of these must be qualified first:

- **Row 20 (mono placement).** A specialization is emitted by the module whose
  post-mono HIR and summary contain it. The summary step's placement is authoritative, so
  workers never re-run mono and cannot duplicate a symbol. This still needs the
  `mir_archive_secondary_keys_v1` collision checks applied to the direct lane.
- **Row 22 (order-dependent counters).** `canonical_type_symbols` and
  `mcdc_next_runtime_id` must become order-independent (derived from owner and name)
  before summary lowering can be byte-identical to full lowering. The same blocker already
  applies to today's sharding.
- **Rows 12-14 (process-global registries).** These must be rebuilt from declarations,
  which the archive lane already does via `prescan_module_declarations_v1`.
- **Row 23 (parse-time globals).** These need either an export row or proof that they
  are module-local.
- **Admission authority.** It must stand in for the archive lane's in-process pins
  (`mir_archive_admission_matches_in_scratch_v1`) without weakening them. The disk
  manifest's identity and seal are the replacement, and they cover only the shard lane.

Qualification gate before stage 2 is enabled: on one build, a worker's MIR from
summary-only lowering must be byte-identical (MIR JSON) to its MIR from full lowering, for
every module.

## Risks

- **Projection asserts.** `mir_hir_project_module_in_owned_scope_v1` was written for
  archive-decoded modules inside a scratch scope. Projecting the resident post-mono HIR
  may refuse (for example, codec rejection of an unregistered node). That makes the whole
  summary step fail, so workers fall back.
- **Decoder correctness.** The decoder is hand-written. A field mismatch shows up as a
  re-encode inequality, which is a refusal and not a wrong admission. The decoder has
  only been exercised on empty-declaration fixtures.
- **Summary step cost.** It is one extra full front half (one ~16 GB process) run serially
  before the workers. Stage 1 adds cost and gains nothing until stage 2 lands.
- **Admission memory.** Admission decodes every record in one scratch scope. That memory
  is reclaimed at scope end, but peak worker RSS rises during admission.

## Files

- `src/compiler/50.mir/hir_declaration_decoder_v1.spl`: decoder and the proving decode.
- `src/compiler/80.driver/driver_build/native_mir_shard_export_v1.spl`: record and
  manifest format, write, read, admit.
- `src/compiler/80.driver/driver_mir_shard_export_v1.spl`: driver producer and admission.
- `src/compiler/80.driver/driver_aot_pipeline.spl`: write-step hook and worker admission.
- `src/app/cli/native_build_main.spl`: `run_mir_shard_export_summaries`.
- `test/01_unit/compiler/driver/native_mir_shard_export_spec.spl`: round-trip and refusals.
