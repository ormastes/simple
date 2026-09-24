# Linker / Loader Inventory for the Pure-Simple mold-based MDSOC++ Linker (2026-09-18)

Read-only audit. Worktree `simple-rc1-share` @ `cc205ae0778` (origin/main + rc1 lanes).
Companion to the proposal `doc/01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md`
(untracked; the only place `LinkRequestV1` / `LinkExecutionPolicyV1` / `LinkEngineFacetV1` appear — no name collision).
Method: `/usr/bin/grep -rn` caller search over `src/` + `test/` (the wrapped `grep` honours .gitignore and under-reports).
"Live" means a production call path from `src/app` / `80.driver` / runtime startup was found; spec-only callers = Unwired.
`L/` = `src/compiler/70.backend/linker/`.

## (a) One-screen summary

1. **No internal linker runs today.** Every production link goes through
   `linker_wrapper.link_to_native` → `L/_LinkerWrapper/native_linking.spl:225` → `link_native_unix` (:273) →
   `L/mold.spl:704 find_linker_path()`: `SIMPLE_LINKER` override, else **mold > ld.lld > ld > cc fallback**, run as an
   external process via `execute_linker`. Cross targets go straight to cc (:281). Windows → `msvc.spl` (`link.exe`).
2. **An internal-linker skeleton exists but is spec-only**: `elf_parser` 431, `_ElfWriter` 861 (ET_REL writer only),
   `reloc_engine` 279, `sym_resolver` 187, `archive_parser` 396, `object_resolver` 220, `symbol_analysis` 211.
   The callers are only `test/{01_unit,unit}/compiler/backend/linker/*_spec.spl`. It does not produce runnable executables.
3. **The in-process LLD bridge is a stub.** `lld_sffi.spl` dlsyms `simple_lld_elf_link` and returns 127 if missing.
   `lld_shim.cpp` appears in no CMake, `.shs`, `.sh`, `.rs` or `.sdn` build input, so it is never compiled.
4. **The loader already does real linking, live**: `99.loader/module_loader_compat.spl` (1905) parses SMF via
   `L/smf_reader_memory`, copies symbols into executable memory, **applies relocations (types 1-5) inline**
   (:1324-1370), and resolves `main` (:1851). This is reached from `bin/simple run` (`app/io/_CliCommands/run_commands.spl:109`).
5. **Relocation application exists 4 times** (loader inline, `os/smf/smf_dynlib.spl:759`, `99.loader/loader/object_mapper.spl:264`,
   `L/reloc_engine.spl:135`) plus `gpu_smf/smf_reloc_apply`. **Symbol resolution exists 4+ times** (`sym_resolver`,
   `99.loader/settlement/linker.spl`, `gpu_smf/smf_link_profile:164`, loader `LoadedSymbol` dicts).
6. **ELF read/write is duplicated across 5 owners**: linker (`elf_parser`, `elf_inspect`, `_ElfWriter`), backend
   (`backend/native/elf_writer.spl` 479 + `native_elf`), driver (`80.driver/smf_elf_parser.spl` 249), and the SimpleOS kernel
   (`os/kernel/loader/elf64.spl` 387, `elf_loader`). **SMF writers: 2** (`L/smf_writer` 844 and `80.driver/smf_writer` 773, where the driver
   one wraps the linker one). **SMF readers: 3+** (`smf_reader` 630, `_SmfReaderMemory` 921, `os/kernel/loader/smf.spl` 352, and the dead `arch_validator`).
7. **The structural link manager contract (L0-L12) has types but no implementation.** `src/lib/common/structural/resolve/resolve_types.spl`
   (`ResolveProfile` trait :253, `SMF_LINK_STAGE_L0..L12` :275-287) has **zero `impl ResolveProfile`**. The CPU SMF slice
   `L/gpu_smf/*` (1172 LOC, L2/L4/L6/L7/L8 + receipts) has no caller outside its own directory.
8. **KPF / MDSOC++ sealer is ready to reuse but has never run in production**: `src/lib/mdsocpp/seal.spl:48 mdsocpp_seal_v1`
   (capsules, facet binding, topological start order, `memory_budget_bytes`). Its only caller is `test/01_unit/lib/mdsocpp/seal_spec.spl`.
9. **SOSIX lacks three things a bounded linker needs**: mmap file windows, a parallel/thread API, and memory limits.
   pread/pwrite exist (`sosix/posix.spl:39,43` → `rt_fd_pread/pwrite`). Spawn exists (`host_facade.spl:135`).
   RSS accounting is `ps -o rss` (`host_facade.spl:100`).
10. **No remote loader exists.** All grep hits are false positives (scheduler `remote_load`, font loading).
11. **Old plans contradict the proposal in 7 places.** "Native stays on established linkers", "MoldBackend delegates to an external process",
    and the in-guest lld ladder are the main ones (see (d)).

## (b) Inventory

### b1. Linker — `src/compiler/70.backend/linker/`

| path (lines) | what | status | callers evidence | reuse |
|---|---|---|---|---|
| `_LinkerWrapper/native_linking.spl` (1364) | platform dispatch, arg building, rpath, macOS cc path | **Live** | `backend/llvm_native_link_orchestrator.spl:648`, `80.driver/driver_aot_native_output.spl:2278`, `build_native_types.spl:88` | EXTEND: becomes the "external engine" facet and the fallback |
| `_LinkerWrapper/shared_linking.spl` (385), `native_all_support` (166), `archive_retention` (55) | shared-lib link, native-all | **Live** | `driver_aot_native_output.spl:2205`, `app/compile/lua_shared_lib.spl:112` | EXTEND |
| `linker_wrapper.spl` (25) | re-export facade | Live | as above; `driver_aot_smf_output.spl:138,169` (`link_to_smf`, `link_to_self_contained`) | REUSE (entry point to keep) |
| `linker_wrapper_helpers.spl` (413) | file output / write helpers (L11: whole-file sync write :328,368) | Live | `native_linking:60-66`, `00.common/backend_plugin/builtin_adapter.spl:19` | EXTEND (range writes) |
| `linker_wrapper_lib_support.spl` (481) | lib resolution, single-pass archive (:304) | Unwired | specs only | REPLACE by an L5 archive fixpoint |
| `mold.spl` (803) | find mold/lld/ld, `execute_linker`, CRT probe | **Live** | `native_linking:45-46`, `shared_linking` | EXTEND (engine selection). `mold_post_link_check`, `write_elf_object`, `parse_linker_diagnostics`: 0 callers → DELETE-CANDIDATE |
| `mold_compatibility.spl` (119) | mold feature tables | Dead | 2 specs | DELETE-CANDIDATE / fold into proposal feature matrix |
| `link.spl` (639) | older `Linker`/`LinkConfig`, `BackendSystemLinker`, `auto_detect_linker` | Partial | only `LinkConfig` type imported (`mold.spl:20`, `msvc`, `native_linking`) | REPLACE `LinkConfig` with `LinkRequestV1`; delete rest |
| `msvc.spl` (486) | `link.exe` wrapper | Live (Windows) | `native_linking:61` | REUSE as COFF external engine |
| `crt_discovery.spl` (243) | `cc -print-file-name` CRT probe | Live | `native_linking:57`, `shared_linking` | REUSE; `mold.mold_find_crt_files` is Duplicate-of-crt_discovery |
| `platform_defaults.spl` (202) | per-OS link data, `elf_emulation` | Live | `native_linking:53`, `crt_discovery`, `link_deps` | REUSE |
| `link_deps.spl` (205) | defaults + SDN merge | Unwired | only `app/cli/check_links.spl:6` (not in dispatch table) | EXTEND or DELETE |
| `lld_sffi.spl` (94) + `lld_shim.cpp/.h` (83) | in-process LLD via dlsym | **Stub** (returns 127, shim never built) | `native_linking:44,453` (SimpleOS), `shared_linking:27` | REPLACE with the pure-Simple engine; delete once the SimpleOS path moves |
| `elf_parser.spl` (431) | ELF64 object parse | Unwired | internal linker + 11 specs | EXTEND → ELF capsule reader (single owner) |
| `elf_inspect.spl` (254) | ELF header inspection | effectively Dead | `mold.spl:16` only for uncalled `mold_post_link_check:781` | merge into elf_parser |
| `elf_writer.spl` (10) + `_ElfWriter/{encoding 517, writer 344}` | ET_REL object writer | Unwired | `elf_writer_spec` only | EXTEND to ET_EXEC/ET_DYN output, or merge with `backend/native/elf_writer` |
| `reloc_engine.spl` (279) | ELF reloc apply (L8, :135-216) | Unwired | `reloc_engine_spec` ×2 only (verified) | EXTEND → ELF capsule reloc |
| `sym_resolver.spl` (187) | symbol resolution | Unwired | specs only | merge with `settlement/linker` into the L4 owner |
| `archive_parser.spl` (396) | `ar` parse | Unwired | specs only | REUSE (L5 input) |
| `object_resolver.spl` (220) | object → symbol resolve | Unwired | `linker_wrapper_lib_support` (spec-only) | merge |
| `symbol_analysis.spl` (211) | reachability/GC (L6 :65-141) | Dead | 3 specs | merge with `gpu_smf/smf_reachability` |
| `pe_parser` (308), `pe_inspect` (307) | PE/COFF parse | Dead | 0 / pe_parser only | EXTEND → COFF capsule; also duplicates `src/lib/{,common/}pe_coff_header.spl` |
| `macho_parser` (383), `macho_inspect` (223) | Mach-O parse | Dead | `macho_roundtrip_spec` only | EXTEND → Mach-O capsule; writer lives in `backend/native/macho_writer.spl` (598) |
| `linker_script.spl` (621) | GNU ld script parser (ENTRY/MEMORY/SECTIONS) | Dead | specs only | REUSE for boot-layout provider (read `.ld`) |
| `linker_context` (72), `lazy_instantiator` (334) | link-time instantiation | Dead | only `link.spl` / each other | DELETE-CANDIDATE (JIT instantiation lives in `99.loader/jit_instantiator`) |
| `wasm_linker.spl` (134) | `wasm-ld` wrapper | Dead | 0 callers | DELETE-CANDIDATE or WASM external facet |
| `smf_reader_memory` (14) + `_SmfReaderMemory/{header_parser 668, symbol_parser 253}` | SMF in-memory parse | **Live** | `99.loader/module_loader_compat:21`, `smf_segment_load:13`, `aspect_pack_section:15`, `os/smf/smf_dynlib.spl:2` | REUSE → SMF capsule reader (single owner) |
| `smf_reader.spl` (630) | SMF file reader | Live (via obj_taker) | `99.loader/loader/object_provider:11` | merge with smf_reader_memory |
| `smf_writer` (844), `smf_header` (526), `smf_enums` (210), `smf_getter` (426) | SMF write/header/getter | **Live** | `80.driver/smf_writer.spl:19,28`, `smf_binary_helpers:9`, `smf_hooks:13`, `native_linking:50` | REUSE → SMF capsule writer |
| `lib_smf` (434), `lib_smf_reader` (247), `lib_smf_writer` (367) | library SMF | Live | `app/io/_CliCompile/compile_opt_and_driver.spl:12`; internal via smf_getter/object_provider | REUSE |
| `obj_taker` (770), `object_provider` (230), `object_code_unit` (15), `object_emitter` (98) | object intake for native link | **Live** | `build_native{,_types,_pipeline}`, `module_loader_compat:22`, `native_linking:47-52` | REUSE → L0/L1 input stage |
| `object_provider_adapter` (6) | imports non-existent `compiler.loader.object_provider` | Dead/broken | 0 | DELETE-CANDIDATE |
| `smf_source` (41) | SMF source | Dead | specs; duplicates `os/smf/smf_jit_bridge.spl:1 SmfSource` | DELETE-CANDIDATE |
| `swa`, `swa_reader`, `swa_writer`, `swa_zip`, `swa_zip_reader` (362/295/493/211/221) | web-app archive | Unwired | only `test/03_system/infrastructure/web_app_packaging_spec.spl` | out of scope (not a linker concern) |
| `gpu_smf/*` (8 files, 1172) | CPU SMF link slice L2/L4/L6/L7/L8 + receipts | Unwired | specs + `style_link_profile`; no external importer | **EXTEND → SMF capsule engine** (closest to the contract) |
| `__init__.spl` (258), `mod.spl` (35) | package facade / comments | Dead (0 importers; duplicate `SelfContainedConfig`/`fnv1a_hash` exports) | — | DELETE-CANDIDATE |

**Outside `L/`**

| path | what | status | reuse |
|---|---|---|---|
| `src/app/linkers/main.spl` (81) | `simple linkers` CLI | Live (`dispatch/table.spl:42`, `command_registry.spl:44`) | EXTEND (show engine/capsule matrix) |
| `src/app/linker_gen/*` (707) | SDN board → `.ld` generator | Unwired (not dispatched; 2 open bugs `doc/08_tracking/bug/linker_gen_*_2026-09-06.md`) | EXTEND → SimpleOS boot-layout provider |
| `src/app/cli/check_links.spl` | link deps check | Unwired (not dispatched) | fold into `linkers` |
| `src/lib/nogc_sync_mut/platform/linker.spl` (40) | `SystemLinker`/`auto_detect_linker` | Live via `platform/__init__:8` | Duplicate-of `L/link.spl` → DELETE-CANDIDATE |
| `src/compiler/70.backend/backend/native/{elf_writer 479, native_elf, elf_writer_serialize, macho_writer 598}` | codegen object writers | Live (`build_native_pipeline`, `85.mdsoc/construct/asm`, `os/kernel/loader/process_image`) | single ELF/Mach-O writer owner candidate |
| `src/compiler/70.backend/baremetal/link_wrapper.spl`, `backend/simpleos_native_linkers.spl` | baremetal/SimpleOS link | Live consumers of `.ld` | EXTEND (boot-layout consumer) |
| `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` | seed linker selection (probes bare `ld.lld`, :1972) | Live for bootstrap | out of scope (seed); keep parity |
| `src/os/kernel/arch/*/linker.ld` (+ realtime, baremetal lib, 70.backend/baremetal, cortex_m33) | ~25 hand-written scripts | Live, none generated | boot-layout provider input |

### b2. Loader — `src/compiler/99.loader/`

| path | what | status | callers | reuse |
|---|---|---|---|---|
| `module_loader_compat.spl` (1905) | SMF runtime loader: load, symbol copy, **reloc 1-5** (:1324-1370), `main` call (:1851) | **Live** | `runtime/__init__:10` ← `app/io/_CliCommands/run_commands.spl:9,109` | EXTEND: route its reloc loop to the shared reloc owner |
| `smf_mmap_native.spl` | `rt_mmap_raw`/`rt_mprotect`, `native_reloc_write_i32/i64` | Live | `module_loader_compat:23`, `os/smf/smf_dynlib:8`, `parser_structural_mask_mapper_v1:7` | REUSE (reloc write primitive) |
| `segment_mapper.spl` | W^X segment mapping, `begin_relocation` :386 | Live | `os/smf/smf_dynlib.spl:7,257` | REUSE |
| `jit_instantiator` + `jit_context` | template JIT from SMF metadata | Live | `70.backend/codegen.spl:694,701` ← `80.driver/driver_pipeline_execution:57` | out of scope |
| `smf_segment_load.spl`, `aspect_pack_section.spl` | section extents / aspect packs | Live | `module_loader_compat:24`, `L/smf_writer` | REUSE |
| `metadata_symbols.spl` | instantiation symbol names | Live (internal) | `module_loader_compat:10` | keep |
| `settlement/linker.spl`, `settlement/builder.spl` | **cross-module resolver** (`resolve` :157, `resolve_with_fallback` :186, `RelocationKind` :68). Builder writes its own "SSMF" (:184) | Unwired | `settlement_linker_cardinality_spec`, `settlement_exports_contract_spec` only | EXTEND → L4 resolve owner (closest pure-Simple resolver) |
| `loader/object_mapper.spl` | `apply_smf_relocations` :264 | Unwired | `reloc_apply_spec`, `object_mapper_spec` | merge into the reloc owner |
| `module_resolver/resolution.spl` | module path resolution :433, :524 | Unwired externally (`app/var/main.spl:14` imports a stale path) | — | out of scope (source modules, not symbols) |
| `loader/module_loader.spl` (875) | old copy of `moduleloader_execute_smf` | **Dead** (broken relative imports :21) | 0 | DELETE-CANDIDATE |
| `loader/smf_cache.spl`, `loader/arch_validator.spl` | SMF header re-parse (`arch_validator` :119 has its own 128-byte header parse) | Dead | 0 | DELETE-CANDIDATE |
| `runtime/package_image_entrypoint.spl` | imports non-existent `compiler.loader.shared_contract` (:10) | Broken | tests | fix or delete |
| `generation_sweeper`, `mod`, `module_loader_lib_support`, `resource_lifecycle`, `smf_cache_manager` | empty files | Dead | — | DELETE-CANDIDATE |
| `completeness_seal/*`, `provider_admission/*`, `unload_*`, `reload_rebuild` | admission/lifecycle policy | Live / partly unwired | `app/check/completeness_seal_census.spl:35-55` | not linking; seal pattern reusable |

Also live dynamic loading outside 99.loader: `src/os/smf/smf_dynlib.spl` (reloc loop :759-772), `os/smf/dynsmf_*`, and
`os/kernel/loader/{elf64, elf_loader, smf, segment_mapper, process_image}` (SimpleOS in-kernel ELF/SMF loader).

### b3. Remote loader

None exists. The `remote_load` hits are scheduler work-stealing (`os/kernel/scheduler/green_worker.spl:80`, Lean proofs),
`@font-face` network loading in browser docs, and a size note. Nearest is the debug `CodeUploader`
(`lib/nogc_sync_mut/debug/remote/exec/uploader`, used by `exec/manager.spl:14`), which is unrelated to SMF.
**Gap**: if the proposal needs remote capsules, it is new work, with no duplication risk.

### b4. Interpreter — `src/compiler/95.interp`

No linking, relocation or dlsym. Function binding is a name → `MirFunction` dict (`mir_interpreter.spl:63`, `set_function_table`
:313, lookup :334). An unknown call silently yields 0 (:463), a latent defect. Externs are static `extern fn rt_*`
(`mir_interp_runtime.spl:12-18`), and the JIT runs through `rt_jit_*` (`execution/tiered_jit_manager.spl:12-22`). It imports nothing from 99.loader.
**No overlap.**

### b5. KPF / MDSOC++ foundation

| path | what | status | reuse for linker |
|---|---|---|---|
| `src/lib/common/kernel_plugin/contracts.spl` (:67-146) | `KpfMemoryContractV1`, `KpfConcurrencyContractV1`, `KpfTrustContractV1`, validators, lifecycle FSM | Implemented | REUSE: fast vs bounded variant = two memory contracts |
| `src/lib/common/kernel_plugin/schema_header.spl:39-74` | `KpfSchemaHeaderV1` (72 B, id/major/minor/digest) + validator | Implemented | REUSE as header for `Link*V1` |
| `src/lib/mdsocpp/{model.spl:38-92, seal.spl:48}` | `CapsuleDescriptorV1`, `MdsocppSealPolicyV1.memory_budget_bytes`, `mdsocpp_seal_v1` (facet binding, topological start, budget sum :40-46) | Implemented, **spec-only** (`seal_spec.spl:34-72`) | REUSE for ELF/COFF/Mach-O/SMF capsules; the linker would be its first production caller |
| `src/lib/nogc_sync_mut/kernel_plugin/static_registry.spl:4-20` | static binding registry | only `app/test/kpf_cross_placement_conformance.spl:26` | REUSE (static capsule set) |
| `nogc_async_mut/kernel_plugin/runtime.spl:64-211`, `nogc_async_mut_noalloc/kernel_plugin/fixed_runtime.spl:81` | session/ring runtime, fixed runtime | Implemented | optional (link-as-service) |
| `src/tool/kernel_plugin_schema/` (826) | schema → C/Rust/C++/WIT/Simple generator | Implemented | REUSE to generate `Link*V1` bindings |
| `00.common/backend_plugin/kpf_adapter.spl:48` | backend plugin ABI → KPF header | re-exported, no call site | pattern to copy |

Plan status: `kernel_plugin_fabric.md:3` "Active implementation" (S0, A1 done; E2-E5 not published; **no linker lane**).
`kernel_plugin_migration_plan.md:3` "ACTIVE; NOT COMPLETE" (Phase 7 runtime rows blocked).

### b6. SOSIX host capabilities

| capability | API | status | gap |
|---|---|---|---|
| positioned read/write | `sosix/posix.spl:39,43` → `sffi/fs.spl:138,147` → `rt_fd_pread/pwrite` (`runtime_native.c:12978,12984`) | Implemented; no caller outside sosix | usable for L11 range writes |
| ring file ops | `sosix/fs.spl:105,108`, `sync.spl:97,103` | reference provider does open+pread+close per operation, no errno; io_uring TODO C4, mac/win TODO C5 (`file_driver.spl:7-16`) | too slow for a linker hot path |
| mmap file windows | not in SOSIX; `nogc_sync_mut/io/file_ops.spl:356 file_mmap` → `rt_mmap` (the interpreter aborts on the extern :362-364; seed stub `stubs.rs:145`) | Partial | **GAP**: `sosix_map_window(fd, off, len, prot)` |
| threads / parallel | not in SOSIX; `nogc_sync_mut/concurrent/thread.spl:87-89` | outside SOSIX | **GAP**: parallel-for / worker pool capability |
| process spawn | `host_facade.spl:76 sosix_run`, `:135 sosix_spawn` | Implemented (`app/jj/diff.spl:6`) | REUSE for the external-engine facet |
| memory accounting | `host_facade.spl:86 sosix_proc_usage` (`ps -o rss`, :100); `rt_fork_parent_peak_rss_bytes` | crude, no limit API | **GAP**: RSS budget + setrlimit/arena cap for ≤6 GB |

Design: `doc/05_design/runtime/sosix_runtime_unification_design.md:4` "Ready for implementation"; its pread/pwrite contract is at :93.

## (c) Duplication map (concern → copies → recommended single owner)

| concern | copies (file:line) | owner recommendation |
|---|---|---|
| ELF object/exec **parse** | `L/elf_parser` (431), `L/elf_inspect` (254), `80.driver/smf_elf_parser.spl` (249), `os/kernel/loader/elf64.spl` (387) + `elf_loader` | ELF capsule reader in `L/` (from `elf_parser`). The kernel keeps a noalloc subset but shares a `common` header codec |
| ELF **write** | `L/_ElfWriter` (861, ET_REL), `backend/native/elf_writer.spl` (479) + `elf_writer_serialize` | one ELF writer; the linker capsule extends the live `backend/native` one or vice versa, never both |
| PE/COFF parse | `L/pe_parser`, `L/pe_inspect`, `src/lib/{,common/}pe_coff_header.spl` | COFF capsule; the lib header becomes the shared codec |
| Mach-O | `L/macho_parser`, `L/macho_inspect`, `backend/native/macho_writer.spl` | Mach-O capsule (read + write together) |
| SMF read | `L/smf_reader` (630), `L/_SmfReaderMemory` (921), `os/kernel/loader/smf.spl` (352), dead `99.loader/loader/arch_validator:119`, `loader/smf_cache` | `_SmfReaderMemory` (the live one) = SMF capsule reader; fold `smf_reader` into it |
| SMF write | `L/smf_writer` (844), `80.driver/smf_writer.spl` (773, imports L's :28), `settlement/builder:184` ("SSMF" variant) | `L/smf_writer`; the driver one is a thin adapter; SSMF becomes a mode or is deleted |
| SMF contract/header | `L/smf_header` (526), `os/smf/smf_header_contract.spl` (192) | one header contract in `common` |
| **Relocation apply** | `module_loader_compat.spl:1324-1370` (live), `os/smf/smf_dynlib.spl:759-772` (live), `99.loader/loader/object_mapper.spl:264`, `L/reloc_engine.spl:135-216`, `L/gpu_smf/smf_reloc_apply` | one pure reloc-formula module (`gpu_smf/smf_reloc_formulas` or `reloc_engine`) used by both the static linker (L8) and the loader, writing through `smf_mmap_native.native_reloc_write_*` |
| **Symbol resolve** | `L/sym_resolver`, `L/object_resolver`, `99.loader/settlement/linker.spl:157`, `L/gpu_smf/smf_link_profile.spl:164`, loader `LoadedSymbol` dicts | L4 owner = `settlement/linker` semantics + `gpu_smf` receipts, behind `ResolveProfile` or `LinkEngineFacetV1` |
| Reachability / GC | `L/symbol_analysis:65-141`, `L/gpu_smf/smf_reachability` | gpu_smf (L6) |
| Archive handling | `L/archive_parser` (unwired), `linker_wrapper_lib_support:304` single-pass | archive_parser + L5 fixpoint |
| Linker selection / detect | `L/mold.spl:704`, `L/link.spl auto_detect_linker`, `lib/nogc_sync_mut/platform/linker.spl`, seed `linker.rs:1972` | `mold.find_linker_path` → engine-selection facet; delete the other two Simple copies |
| CRT discovery | `L/crt_discovery`, `L/mold.mold_find_crt_files` | crt_discovery |
| Linker script | `L/linker_script` (parser, dead), `app/linker_gen` (generator, unwired), `baremetal/link_wrapper` (consumer) | boot-layout provider owns both parse and generate |
| Link config type | `L/link.spl LinkConfig`, `NativeLinkConfig`, `MoldConfig`, `SelfContainedConfig` (twice in `__init__`) | `LinkRequestV1` + `LinkExecutionPolicyV1` |
| Contract naming | `ResolveProfile`/`ResolveKey`/`ResolveMode` (frozen v1) vs proposed `LinkEngineFacetV1` | pick one (see d) |

## (d) Contradictions between old plans and the proposal

1. `doc/03_plan/platform/structural_compute/link_manager_plan.md:23-25`: "Native ELF/Mach-O/PE stays on established native
   linkers (mold does not emit SMF)". The proposal makes native formats in-process pure-Simple capsules. **Supersede explicitly.**
2. `doc/05_design/compiler/architecture/mold_mimalloc_compatibility_surface.md:17,19,20`: `MoldBackend` "delegates to external
   mold/lld/ld"; installs upstream mold "not a source reimplementation"; `mold_is_pure_simple_linker_complete` returns false.
   That false flag is the natural completion gate for the proposal, so reuse it rather than adding another.
3. `L/lld_sffi.spl:1-5` makes the SimpleOS path an in-process LLD via C++ shim. That conflicts with "pure Simple" and the shim is never built. Retire it.
4. `doc/03_plan/os/in_guest_lld_link_ladder.md:23-24` plus `toolchain_selfhost_bootstrap_plan.md:69 C4_lld_link_ladder` make in-guest
   self-host linking depend on static `/LLD.ELF` ("NOT YET BUILT", "PREPARED-POSTPONED"). The proposal would replace C4, and that plan must be amended.
5. `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md:72`: "No in-guest linking in Phase 1. ld/lld needs fork too". A pure-Simple
   linker linked into `simple` removes the fork dependency. Note it as an enabler, not a conflict to ignore.
6. `link_manager_contract_v1.md:13` is frozen v1 with owner `src/lib/common/structural/resolve/` and names `ResolveProfile`/`ResolveKey`/`ResolveMode`.
   The proposal introduces `LinkEngineFacetV1` for the same L4 concern and a different owner path. **Frozen contract: either implement
   `ResolveProfile` as the SMF engine's resolve step, or publish v2. Do not run both.**
7. `.spipe/link_manager/smf_linker_map.md` maps L0-L12 onto `L/`, and `.spipe/link_manager/state.md:178-182` says the next step is wiring
   L2-L8 into a driver, blocked on architecture-owner decisions. The proposal must take over this lane, not open a parallel one.
8. `kernel_plugin_fabric.md` has no linker lane, and its rule is "V1 schema… one exclusive owner". The linker needs a new KPF lane or a handoff request.
9. `linker_script_gen_design.md` (Draft) targets GNU ld/lld as the consumer of generated scripts. The boot-layout provider changes that consumer.

No prior doc sets a link-job memory bound (only `QEMU_MEM=2G`+ for clang lanes), so ≤6 GB does not conflict with anything.

## (e) Gaps the proposal must fill

1. **Executable output**: no Simple code writes ET_EXEC/ET_DYN with program headers, PLT/GOT, TLS, dynamic section,
   `.eh_frame_hdr` or build-id. `_ElfWriter` is ET_REL only.
2. **Wiring**: nothing selects an internal engine. `find_linker_path` (`mold.spl:704`) needs an `internal` engine option behind
   `SIMPLE_LINKER`, with the external engines kept as fallback facets and a parity check against mold output.
3. **L5 archive fixpoint, L3 intern/sort, L10 provenance, L12 manifest commit**: absent (`smf_linker_map.md:155-167`).
4. **L11 output**: whole-file sync write today. Needs pwrite range writes (SOSIX pread/pwrite exists) and mmap windows (missing).
5. **Bounded variant enforcement**: the seal checks `memory_budget_bytes` on paper only. There is no RSS limit API and no arena cap in SOSIX.
6. **Parallelism**: no SOSIX thread/parallel-for capability. The mold-style fast variant depends on it.
7. **First production caller for `mdsocpp_seal_v1` / `KpfSchemaHeaderV1`** under the linker. Neither is exercised outside specs today.
8. **Loader convergence**: the 2 live inline reloc loops (`module_loader_compat:1324`, `smf_dynlib:759`) must move onto the shared
   reloc-formula owner, or the linker becomes copy #6.
9. **COFF/Mach-O**: parsers exist but are dead. No COFF writer exists, and no Mach-O linking exists. The macOS path is `cc`/ld64
   (`native_linking.spl:1051-1061`).
10. **Seed parity**: `compiler_rust/.../native_project/linker.rs` keeps its own selection. The bootstrap still links with the external linker until
    the self-hosted binary links itself.
11. **Cleanup debt before building** (DELETE-CANDIDATEs above): `L/__init__.spl`, `L/mod.spl`, `object_provider_adapter`, `smf_source`,
    `linker_context`, `lazy_instantiator`, `wasm_linker`, `99.loader/loader/module_loader.spl`, `arch_validator`, `loader/smf_cache`,
    5 empty loader files, and `lib/nogc_sync_mut/platform/linker.spl`.
