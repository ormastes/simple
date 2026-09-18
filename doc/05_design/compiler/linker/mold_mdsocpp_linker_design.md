# mold-based MDSOC++ Linker — Design

**Date:** 2026-09-18 · **Status:** Proposed (architecture decisions; no code landed)
**Worktree:** `simple-rc1-share` @ `cc205ae0778` · **Host used for reading:** aarch64 (`bin/release/aarch64-unknown-linux-gnu/simple`)
**Inputs:** research `doc/01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md` (R-doc),
audit `doc/01_research/compiler/linker/linker_loader_inventory_2026-09-18.md` (I-doc),
frozen `doc/05_design/platform/structural_compute/link_manager_contract_v1.md` (C1).
**Plan:** `doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md`.
`L/` = `src/compiler/70.backend/linker/`, `LD/` = `src/compiler/99.loader/`.

## 0. Decisions in one screen

| # | Decision | Why |
|---|---|---|
| D1 | One owner per concern (§2); everything else becomes a thin adapter or is deleted (§3) | I-doc §(c): 5 ELF owners, 5 reloc copies, 4 resolvers |
| D2 | The external-linker path (`mold.find_linker_path` → `execute_linker`) stays the default engine until the internal ELF engine passes G2 parity; receipts always name the engine | R-doc §10 "adapters first"; no fallback counts as completion |
| D3 | `ResolveProfile` v1 is implemented as-is by the SMF engine (L4). `LinkEngineFacetV1` is a **different concern** (job facet), published new. No v2, no mutation of C1 | C1 §4 "profiles share primitives, never semantics"; C1 §1 names `SmfLinkProfile` as the implementation wave |
| D4 | Relocation **values** have one oracle: `L/gpu_smf/smf_reloc_formulas.spl` (reject, never mask). Encoders (ELF bit-fields, SMF bytes, loader memory) call it | Only copy with goldens and overflow rejection; R-doc §11 mutation gate "suppress relocation overflow" |
| D5 | Fast and bounded are two sealed compositions (`link_elf_fast`, `link_elf_bounded`) with two `KpfMemoryContractV1` values; selected once per job | R-doc §4/§9; `mdsocpp_seal_v1` already sums `memory_budget_bytes` |
| D6 | SimpleOS boot images keep `ld.lld -T linker.ld` until `BootLayoutPlan` output boots on QEMU real firmware **and** a board | `.claude/rules/board-runnable.md` |
| D7 | Completion gate = `mold_is_pure_simple_linker_complete()` flipping to `true` (§9). `mold_compatibility.spl` is therefore **not** deleted | Task requirement; I-doc §(d)2 |
| D8 | `LinkRequestV1`/`LinkExecutionPolicyV1`/`LinkReceiptV1` are plain Simple structs in `src/lib/common/linker/`, each carrying `KpfSchemaHeaderV1`; they are **not** added to the S1 schema generator without a handoff | `kernel_plugin_fabric.md` "V1 schema has one exclusive owner" |
| D9 | Remote loader is out of scope; only the seam is named (§4) | I-doc §b3: nothing exists, no duplication risk |

Non-goals: LTO, PDB/dSYM, Windows ARM64, GPU-resident resolve (`ResolveMode` 1/2), a `VirtualObject→VirtualSection→VirtualRelocation` hierarchy, a link daemon.

## 1. Corpus fact that shapes the first slice

Production objects come from the LLVM plugin and are linked **dynamically** (`native_linking.spl:363` `-dynamic-linker`, `:374` `-pie`, `:991` `-z relro -z now --gc-sections`). The pure-Simple native backend emits a much smaller relocation set (`backend/native/elf_writer.spl:78-95`):

| Arch | Native-backend set (verified) | Formula class | Needs GOT/PLT synth |
|---|---|---|---|
| x86_64 | `R_X86_64_64`(1) `PC32`(2) `PLT32`(4) `32S`(11) | S+A, S+A-P | PLT32 → S when static |
| aarch64 | `CALL26`(283) `ADR_PREL_PG_HI21`(275) `ADD_ABS_LO12_NC`(277) `LDST64_ABS_LO12_NC`(286) | bit-field encodings, page arithmetic | no |
| riscv64 | `CALL_PLT`(19) `PCREL_HI20/LO12_I`(23/24) `HI20/LO12_I`(26/27) | **paired** hi/lo | no |

Therefore: **slice 1 = static ET_EXEC over native-backend objects** (x86_64 + aarch64), **slice 2 = the LLVM corpus** (adds GOTPCREL(X), TLS, `.dynamic`, DT_NEEDED, PLT/GOT synthesis, `.eh_frame_hdr`, build-id). G0 captures the real set with `llvm-readelf -r` over the corpus; nothing in this doc guesses it.
`L/reloc_engine.spl` today applies only NONE/ABS64/ABS32/CALL26 on aarch64 (`:167-178`) and **masks** on `R_X86_64_32` (`:150`) — it cannot relocate the native backend's own aarch64 output yet.

## 2. Owner map (one owner per concern)

| Concern | Owner (wins) | Becomes thin adapter | Merged/deleted | Stage |
|---|---|---|---|---|
| ELF read (obj + exec headers) | `L/elf_parser.spl` (`elf_parse_object`, `elf_parse_symbols`, `elf_parse_relocations`) | `80.driver/smf_elf_parser.spl` keeps only ELF-reloc→SMF-wire mapping, calls `elf_parser` | `L/elf_inspect.spl` → merged (only user is uncalled `mold_post_link_check`) | L1 |
| ELF read, kernel | `src/os/kernel/loader/elf64.spl` stays (noalloc/kernel closure; cannot import `70.backend`) | — | parity by shared golden fixtures, not shared code | — |
| ELF byte codec | `L/_ElfWriter/encoding.spl` (`emit_elf_header`, `emit_section_header`, `emit_symbol`, `emit_relocation`, `StringTableBuilder`, `write_u*_le`), imported only through the 10-line facade `L/elf_writer.spl` (same pattern as `smf_reader_memory.spl` ↔ `_SmfReaderMemory/`) | `backend/native/elf_writer.spl` (live ET_REL owner) re-bases onto the codec | `L/_ElfWriter/writer.spl` (`elf_write_object`, spec-only ET_REL) deleted after its spec moves to `backend/native/elf_writer` | — |
| ELF exec write (ET_EXEC/ET_DYN, PHDRs, synth sections) | **new** `L/elf/elf_exec_writer.spl` over the codec | — | none exists today (I-doc §(e)1) | L9/L11 |
| SMF read | `L/_SmfReaderMemory/{header_parser,symbol_parser}.spl` via `smf_reader_memory.SmfReaderMemory` (live in loader) | `L/smf_reader.spl` (obj_taker path) becomes a file→memory shim; kernel `os/kernel/loader/smf.spl` stays noalloc twin with goldens | `LD/loader/arch_validator.spl`, `LD/loader/smf_cache.spl` deleted | L1 |
| SMF write | `L/smf_writer.spl` (+`smf_header`, `smf_enums`, `smf_getter`) | `80.driver/smf_writer.spl` already wraps it — stays | `LD/settlement/builder.spl` "SSMF" writer deleted | L9 |
| SMF header contract | `L/smf_header.spl` | `os/smf/smf_header_contract.spl` re-exports constants | — | — |
| Relocation **value** | `L/gpu_smf/smf_reloc_formulas.spl` (`smf_reloc_compute`, `smf_reloc_compute_wire`, `smf_reloc_checked_i32/u32`) | `L/reloc_engine.spl` = ELF encoder owner (bit-field/paired patch), calls the formulas for S+A / S+A-P and **adopts reject semantics** | `LD/loader/object_mapper.apply_smf_relocations` deleted | L8 |
| Relocation apply, static bytes | `L/gpu_smf/smf_reloc_apply.spl` (`smf_apply_relocations`, all-or-nothing) | — | — | L8 |
| Relocation apply, runtime memory | `LD/module_loader_compat.spl:1324-1370` and `os/smf/smf_dynlib.spl:759` keep their loops but compute via `smf_reloc_compute_wire`, write via `smf_mmap_native.native_reloc_write_i32/i64` | — | the two inline formula copies | loader |
| Symbol resolve (L4) | `L/gpu_smf/smf_link_profile.spl` (`smf_collect_records`, `smf_resolve`) + receipts (`smf_resolve_with_receipt`) — implements `ResolveProfile` | `L/sym_resolver.spl` = ELF adapter (`ElfObject` → `DefinitionRecord`/`ReferenceRecord`); `LD/settlement/linker.spl` contributes `SymbolVisibility`/`SymbolBinding`/`LinkError` vocabulary then is deleted | `L/object_resolver.spl` deleted (module→object lookup, unwired) | L4 |
| Reachability / GC (L6) | `L/gpu_smf/smf_reachability.spl` (`smf_reachable_sections`) | — | `L/symbol_analysis.spl` deleted (keeps 3 specs' fixtures as goldens) | L6 |
| Archive parse + closure (L5) | `L/archive_parser.spl` (`ar_parse`, `ar_parse_symbol_index`) + **new** fixpoint in `L/elf/archive_closure.spl` | — | `linker_wrapper_lib_support.spl:304` single pass replaced | L5 |
| Section layout (L7) | `L/gpu_smf/smf_section_layout.spl` (`smf_layout_sections`, overflow-exact) extended with segment/PHDR planning for ELF | — | — | L7 |
| Engine selection | `L/mold.spl` `find_linker_path` (adds `internal` alias behind `SIMPLE_LINKER`) | `src/lib/*/platform/linker.spl` twins stay (lib cannot import compiler; `os/port/simpleos_multiplatform_build.spl` consumes) | `L/link.spl` `auto_detect_linker`/`Linker`/`BackendSystemLinker` deleted; only `LinkConfig` survives until `LinkRequestV1` lands | — |
| CRT discovery | `L/crt_discovery.spl` | — | `mold.mold_find_crt_files` deleted | — |
| Linker script parse/gen | **one** boot-layout owner `L/boot_layout/` = `L/linker_script.spl` (parser) + `src/app/linker_gen/{parser,main}.spl` (generator) moved beside it | `baremetal/link_wrapper.spl`, `backend/simpleos_native_linkers.spl` consume `BootLayoutPlan` | — | §7 |
| Job contract | `src/lib/common/linker/{link_request_v1,link_policy_v1,link_receipt_v1}.spl` | `NativeLinkConfig`/`MoldConfig`/`SelfContainedConfig` become projections of `LinkRequestV1` | duplicate `SelfContainedConfig` in `L/__init__.spl` deleted with the file | — |

## 3. Delete / merge list (dead first; precondition = 0 non-spec importers re-verified on the landing sha)

| Wave | Path | Bytes | Precondition |
|---|---|---|---|
| 0 (RC1) | `LD/{generation_sweeper,mod,module_loader_lib_support,resource_lifecycle,smf_cache_manager}.spl` | 0 each (verified `wc -c`) | none |
| 0 (RC1) | `L/object_provider_adapter.spl` (imports non-existent module), `L/smf_source.spl`, `L/mod.spl`, `L/__init__.spl` | 340/1260/1599/7629 | 0 importers |
| 0 (RC1) | `L/linker_context.spl`, `L/lazy_instantiator.spl`, `L/wasm_linker.spl` | 2521/13740/4675 | only `link.spl`/each other |
| 0 (RC1) | `LD/loader/module_loader.spl` (broken imports), `LD/loader/smf_cache.spl`, `LD/loader/arch_validator.spl` | 40152/28374/6958 | 0 importers |
| 0 (RC1) | `L/elf_inspect.spl` → fold `elf_parser`; `mold.spl` `mold_post_link_check`/`write_elf_object`/`parse_linker_diagnostics`/`mold_find_crt_files` | — | 0 callers each |
| 1 (post-RC1) | `L/link.spl` minus `LinkConfig`; `L/object_resolver.spl`; `L/symbol_analysis.spl`; `LD/settlement/*`; `LD/loader/object_mapper.spl` reloc half; `L/_ElfWriter/writer.spl` | — | owner in §2 has the spec moved first |
| 1 (post-RC1) | `L/lld_sffi.spl` + `lld_shim.{cpp,h}` | — | **not RC1**: `native_linking:44,453`, `shared_linking:27` import it; removal changes the SimpleOS-target error path. Retire when the internal engine owns that target |
| never | `L/mold_compatibility.spl` | — | owns the completion gate (D7); `mold_compatibility_features` rows become the engine matrix |
| out of scope | `L/swa*` (web-app archive), `LD/jit_*`, `LD/module_resolver/*`, `L/pe_*`, `L/macho_*` (kept dead until G4) | — | — |

## 4. Boundaries: loader / linker / interpreter / remote

| Component | Keeps | Must call | Must not |
|---|---|---|---|
| Static linker (`L/`) | L0–L12 for native + SMF outputs; archive closure, GC, layout, exec writer | §2 owners; SOSIX byte sources (`sosix_posix_pread/pwrite`) | load code, run `main`, touch `LD/` state |
| Runtime loader (`LD/module_loader_compat.spl`, `os/smf/smf_dynlib.spl`) | SMF mapping, W^X (`segment_mapper`), symbol copy, runtime relocation, `main` dispatch, aspect packs, admission | `SmfReaderMemory` (SMF read owner), `smf_reloc_compute_wire` (value owner), `native_reloc_write_*` | archive search, ICF, whole-image layout, LLVM/PDB (`simple --help` stays linker-free) |
| Kernel loader (`os/kernel/loader/{elf64,smf,segment_mapper,process_image}`) | noalloc ELF/SMF image load | shared golden fixtures | import `70.backend` |
| Interpreter (`95.interp`) | name→`MirFunction` dict binding | nothing here | any link/reloc code (no overlap; unknown call → 0 at `mir_interpreter.spl:463` is a separate defect) |
| Remote loader (future, **new**) | seam only: `fetch(uri) → bytes` → `verify digest == manifest digest` → **same** `module_loader_compat` admission path | `SmfReaderMemory`; `completeness_seal`/`provider_admission` | a second reader, a second reloc loop, a transport in this plan |

Loader convergence is a **behaviour change**: loader types 2–4 cast `as i32` (silent truncation) while `smf_dynlib` range-checks; the oracle rejects. Ordering: spec the loader loop as-is (red spec proving truncation) → switch → both loops reject identically.
Wire type 4 (`GotRel32`) is a **latent loader defect, not a style difference**: `80.driver/smf_elf_parser.spl:246` maps LLVM `R_X86_64_GOTPCREL`(9) → wire 4, whose instruction loads *through* a GOT slot, so the value must be `G + A − P` with **S = GOT-entry address** (the `smf_reloc_formulas` header contract). Both live loops pass the symbol address (`module_loader_compat:158-160`, `smf_dynlib_apply_relocation`), which loads the symbol's first 8 bytes instead of its address. Rule pinned: the formulas contract wins; a loader that sees wire 4 must synthesize a per-module GOT slot (8 bytes per referenced symbol, RW, in the mapped segment) or reject. The native backend's own `EncodedReloc.reloc_type` uses ELF numbering (`encode_x86_64.spl:752` `4 = PLT32`) and is renumbered by the same parser table, so it is unaffected. A4a's red spec proves the wrong bytes before A4b changes the loaders.

## 5. mold phases → Simple owners

mold's phase list (from `mold/src/main.cc`, cited by R-doc R07; author's knowledge of mold, not re-fetched):

| mold phase | L-stage | Owner today | Gap |
|---|---|---|---|
| read input files (parallel, mmap) | L0/L1 | `obj_taker`, `elf_parser`, `SmfReaderMemory` | mmap windows (SOSIX) |
| resolve symbols | L3/L4 | `smf_link_profile` (+ `sym_resolver` adapter) | L3 intern/sort absent |
| resolve archive members (fixpoint) | L5 | `archive_parser` | fixpoint absent |
| eliminate COMDAT dups | L4 | — | slice 2 |
| GC sections (`--gc-sections`) | L6 | `smf_reachability` | roots list (§ R-doc 6) |
| ICF | L6 | — | post-G2, address-significance aware |
| scan relocations (decide GOT/PLT/TLS/dynrel) | L8-scan | — | slice 2 |
| create synthetic sections (GOT, PLT, .dynamic, .eh_frame_hdr) | L7 | — | slice 2 |
| compute section sizes / layout / PHDRs | L7 | `smf_section_layout` | segment/PHDR planning |
| copy chunks (parallel) | L9 | `smf_writer` (SMF), new `elf_exec_writer` | range writes (`pwrite`) |
| apply relocations | L8 | `smf_reloc_apply` + `reloc_engine` over formulas | aarch64 field encoders, riscv pairing |
| write (build-id, output) | L11/L12 | `linker_wrapper_helpers` whole-file write | staged ranges, manifest commit, receipt |

Parallelism: mold's per-phase `tbb::parallel_for` maps to a SOSIX worker-pool capability (§6). Until it exists the fast variant is single-threaded and **says so** in the receipt (`max_workers = 1`).

## 6. Contracts

### 6.1 `ResolveProfile` v1 vs `LinkEngineFacetV1` (D3)
- `ResolveProfile` (`resolve_types.spl:253`) is the frozen **L4 step** interface. `SmfLinkProfile` implements it in `L/gpu_smf/smf_link_profile.spl` (collect = `smf_collect_records`, resolve_group = `smf_resolve`, plan_placement/emit = CPU-reference placements). `ResolveMode` stays `CpuReference` only. `RESOLVE_SCHEMA_VERSION` untouched; goldens never edited.
- ELF does **not** implement `ResolveProfile` in slice 1: ELF resolution needs versions/visibility/interposition that `ResolveKey{Hash128,space}` cannot carry without a name sidecar (R-doc §6). ELF keeps private arrays and emits `StageReceipt`s keyed by `SMF_LINK_STAGE_L*` ids. A second profile (`ElfLinkProfile`) is legal under C1 §4 and is decided at G2, not now. No v2.
- `LinkEngineFacetV1` is the **job** facet (`describe_capabilities, inspect_and_plan, create_session, run, cancel, drain, take_result`) — a KPF facet id, not a resolve step. Memory policy is a new axis (`LinkExecutionPolicyV1`), never a `ResolveMode` discriminant (R-doc R04).

### 6.2 Wire records (`src/lib/common/linker/`, plain structs, D8)
| Record | Fields (fixed-width, header first) |
|---|---|
| `LinkRequestV1` | `KpfSchemaHeaderV1` · target{arch,os,abi,object_format,endian,address_width} · inputs manifest digest · output_contract · semantic_profile_digest · runtime_sysroot_digest · required_features bits · layout/debug handles · reproducibility |
| `LinkExecutionPolicyV1` | header · mode Fast/Bounded/Auto · job_memory_limit_bytes · scratch_limit_bytes · max_workers · allowed_placements · enforcement_requirement |
| `LinkReceiptV1` | header · engine id (external path **or** capsule id) · host/target · policy digest · `MdsocppGenerationReceiptV1` · stage receipts · accounting class · measured peak · outcome (`Success/UnsupportedFeature/UnsupportedBudget/IncompleteDebugOutput/InputError/ResourceFailure/Cancelled`) |

Validated by `kpf_validate_schema_header_v1`. Handoff to S1 (`src/tool/kernel_plugin_schema/`) is filed, not assumed.

## 7. KPF product facets (real symbols)

| Piece | Symbol | Use |
|---|---|---|
| Capsule descriptor | `CapsuleDescriptorV1{capsule_id, closure, provided_facets, required_facets, required_capability_bits, memory, concurrency, uses_ecs:false, state_migrations}` (`src/lib/mdsocpp/model.spl`) | one per engine variant: `link_elf_fast`, `link_elf_bounded`, `link_smf`, `link_external` (mold/lld/ld/cc wrapper), `boot_layout`, later `link_coff`, `link_macho` |
| Facet ids | `MdsocppFacetOfferV1{facet_id}` = `LinkEngineFacetV1`, `RelocFormulaFacetV1`, `ByteSourceFacetV1`, `BootLayoutFacetV1` | `required_facets` express the §2 owners, so a second reloc formula provider is a `DuplicateFacet` seal error |
| Memory/concurrency | `KpfMemoryContractV1` (validated by `kpf_validate_memory_contract_v1`), `KpfConcurrencyContractV1` | fast: host-derived budget, `max_workers = n`; bounded: fixed reservation table (§8), `max_workers = admissible_workers` |
| Seal | `mdsocpp_seal_v1(capsules, MdsocppSealPolicyV1{profile: Userland, critical: false, memory_budget_bytes, maximum_concurrent_calls, generation, composition_digest})` | bounded composition sealed with `memory_budget_bytes = 6_000_000_000`; `MemoryBudgetExceeded` is the paper-side gate; the measured gate is §8 |
| Receipt | `MdsocppGenerationReceiptV1{total_memory_bytes, startup_slots, bindings}` embedded in `LinkReceiptV1` | first production caller of the sealer (I-doc §(e)7) |
| Static composition | `nogc_sync_mut/kernel_plugin/static_registry.spl` | `simple` binary ships the static set; `Dyn` closure only for optional packs (COFF/Mach-O/debug) |
| Schema header | `KpfSchemaHeaderV1` + `kpf_validate_schema_header_v1` (`schema_header.spl:23`) | on every `Link*V1` |

Kernel/driver profile (`MdsocppProfile.Kernel`) is not used: the linker is a userland product; the SimpleOS in-kernel loader is not a capsule.

## 8. Fast vs bounded (D5), 6 GB, accounting, SOSIX prerequisites

| Aspect | Fast (`link_elf_fast`) | Bounded (`link_elf_bounded`) |
|---|---|---|
| Compilation | separate composition `src/compositions/linker_fast/` | `src/compositions/linker_bounded/`; shared source via specialization, never a per-reference virtual store |
| Inputs | resident (mmap window when available, else whole read) | windowed `sosix_posix_pread`; no pointers into evicted windows |
| Symbols | resident arrays | partition + spill (`bounded-spill`), after `bounded-stream` |
| Output | whole-file or range `pwrite` | staged ranges, checksummed spill dir (never tmpfs) |
| Selection | `LinkExecutionPolicyV1.mode`; Auto decides **before** execution and records why | fast→bounded = clean restart |

6 GB = 6,000,000,000 bytes, whole job (coordinator + providers + stacks + I/O residency + helpers). Reservation table is the R-doc §9 one (5.20 GB planned, 0.80 headroom); it is a proposal until G3 measures.

| Accounting class | Mechanism | Platform | Status |
|---|---|---|---|
| `QualifiedJobScope` | cgroup v2 created before first input read, descendants included, no swap; judged on peak | Linux | needs SOSIX limit leaf |
| `MeasuredOnly` | `sosix_proc_usage(pid)` (`host_facade.spl:86`, `ps -o rss`) + `rt_fork_parent_peak_rss_bytes` | all | exists; never a pass for G3 |
| `NotCertified` | none | macOS/FreeBSD/Windows/SimpleOS until adapter | receipt says so |

SOSIX prerequisites — **owned by** `doc/03_plan/runtime/sosix_host_interface_only_plan_2026-09-18.md`, which today has lanes H1–H9 and none of these. This design requests three new lanes there (proposed ids H10–H12) and implements none of them here. `host_facade.spl` is H4-exclusive, so each goes in a new file:

| Need | Proposed leaf (new file) | Blocks |
|---|---|---|
| mmap file windows | `sosix/host_map.spl`: `sosix_map_window(fd, off, len, prot) -> SosixWindow`, `sosix_unmap_window` over `smf_mmap_native._sffi_mmap_raw` | fast input residency, bounded windows |
| worker pool | `sosix/host_workers.spl`: `sosix_parallel_for(n, chunk, body)` over `nogc_sync_mut/concurrent/thread.spl` | fast variant `max_workers > 1` |
| memory limit + peak | `sosix/host_mem.spl`: `sosix_job_scope_create(limit_bytes)`, `sosix_job_scope_peak` (cgroup v2 / setrlimit fallback = `MeasuredOnly`) | G3 acceptance |

Until they land: fast = single-threaded whole-file reads; bounded = `pread` windows + `MeasuredOnly` receipts, which **cannot** close G3.

## 9. BootLayoutPlan (board-runnable)

Real scripts to translate (all hand-written, none generated): `src/os/kernel/arch/{x86_64,arm64,riscv64,riscv32,arm32,x86_32}/linker.ld`.

| Construct | Where seen | `linker_script.spl` today | `BootLayoutPlan` field |
|---|---|---|---|
| `ENTRY`, `SECTIONS`, `MEMORY` | all | parsed (`ld_parse_entry/memory/sections`) | `entry`, `regions[]` |
| `PHDRS` + `:phdr` placement | x86_64 `:22` | missing | `segments[]{name, flags}` |
| `AT(ADDR(.x) - 0xFFFFFFFF80000000)` LMA | x86_64 `:39-75` | missing | `sections[].lma_expr` (higher-half bias) |
| `KEEP(*(.limine_reqs*))`, `KEEP(*(.simple.sandbox*))` | x86_64, arm64 | missing | `sections[].keep_patterns[]` → GC roots |
| `(NOLOAD)`, `. += 64K`, `. = ALIGN(2K)` inside section | arm64 `:53-70` | missing | `sections[].noload`, `pad`, inner `align` |
| `OUTPUT_FORMAT`, `PROVIDE`, `ASSERT` | arm64 `:19`, others | missing | `output_format`, `symbols[]`, `assertions[]` |

Owner: `L/boot_layout/` (parser + `app/linker_gen` generator + `BootLayoutPlan`). Consumers: `baremetal/link_wrapper.spl`, `backend/simpleos_native_linkers.spl`. Equivalence ladder, each rung fail-closed: (1) `ld_parse` round-trips every real script (spec); (2) `llvm-readelf -l -S` parity between `ld.lld -T linker.ld` and the internal layout for x86_64 and arm64 kernels; (3) real-firmware QEMU boot (`scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs`, OVMF for x86_64 — never `-kernel`); (4) board boot with identity + serial transcript, or an explicit board-blocked record. The external `-T` path stays the producer until rung 4.

## 10. Contradiction resolutions (I-doc §(d))

| # | Old statement | Resolution | Doc amended |
|---|---|---|---|
| 1 | "Native ELF/Mach-O/PE stays on established native linkers" | Superseded for ELF after G2; Mach-O/PE after G4. Until then true | `doc/03_plan/platform/structural_compute/link_manager_plan.md:23-25` gets a dated "superseded by" note |
| 2 | `MoldBackend` delegates; predicate returns false | Kept as the **external engine capsule** and the completion gate (D7) | `mold_mimalloc_compatibility_surface.md` mold table gains an "internal engine" row per capsule |
| 3 | SimpleOS path = in-process LLD via C++ shim | Retired post-RC1 when the internal ELF engine owns the SimpleOS target; shim stays unbuilt, never built | `L/lld_sffi.spl` header comment + this doc |
| 4 | In-guest self-host depends on `/LLD.ELF` (C4 ladder) | C4 stays the **proof rung** for the external tool; the internal engine adds rung C4b "guest `simple link` links HELLO.ELF"; C5/B4/P1 may depend on either | `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md:69-75`, `doc/03_plan/os/in_guest_lld_link_ladder.md` |
| 5 | "No in-guest linking in Phase 1; ld/lld needs fork" | Enabler, not conflict: a linker inside `simple` needs no fork. Noted, no change to Phase 1 | `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md:72` footnote |
| 6 | Frozen `ResolveProfile` vs proposed `LinkEngineFacetV1` | D3: both, different concerns; no v2 | C1 unchanged; this doc §6 |
| 7 | `.spipe/link_manager/state.md:178-182` next step = wire L2–L8 behind one driver | This lane **takes over** that step (plan lane A2); no parallel lane | `.spipe/link_manager/state.md` gets a handoff entry |
| 8 | KPF fabric has no linker lane; one schema owner | Linker contributes facets only; `Link*V1` are plain structs (D8); S1 handoff filed | `doc/03_plan/agent_tasks/kernel_plugin_fabric.md` ledger gains row "LINK (facets only)" |
| 9 | `linker_script_gen_design.md` targets GNU ld/lld as consumer | Consumer becomes `BootLayoutPlan`; the `.ld` text output is kept as the external-linker projection | `doc/05_design/compiler/architecture/linker_script_gen_design.md` status + consumer section |

## 11. Placement (final)

`src/lib/common/linker/` (contracts) · `L/elf/` (ELF capsule: exec writer, archive closure, reloc scan) · `L/gpu_smf/` (SMF capsule engine, renamed `L/smf_engine/` only after G2 to avoid churn) · `L/boot_layout/` · `L/mold.spl`+`_LinkerWrapper/` (external engine capsule) · `src/compositions/linker_{fast,bounded}/`. Every directory passes the existing closure checker. No new plugin kernel.

## 12. Open questions for the user

1. Slice-1 target: static ET_EXEC over native-backend objects first (this doc), or go straight at the LLVM/dynamic corpus?
2. Accept `Link*V1` as plain structs outside the S1 schema generator until a handoff (D8)?
3. Kernel loader twins (`os/kernel/loader/{elf64,smf}.spl`) stay separate with golden parity — acceptable, or must they share a `common` codec despite the noalloc closure?
4. Is dropping `lld_sffi`/`lld_shim.cpp` (never built) acceptable before the internal engine owns SimpleOS, given it only changes an error message?

**Decided 2026-09-18:** (1) slice 1 = static ET_EXEC over native-backend objects; (2) `Link*V1` plain structs until S1 handoff; (3) kernel loader twins stay separate with golden parity; (4) `lld_sffi`/`lld_shim` retirement deferred to post-RC1 (not in any RC1 lane).
