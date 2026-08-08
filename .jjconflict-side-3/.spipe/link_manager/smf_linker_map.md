# SMF linker map (Lane SMFMAP, read-only scout)

Scope: `src/compiler/70.backend/linker/`, mapped onto the frozen L0–L12 SMF
pipeline stages from `doc/05_design/platform/structural_compute/link_manager_contract_v1.md`
§4, per `doc/03_plan/platform/structural_compute/link_manager_plan.md`.
No code was modified. All line numbers verified against the working tree on
2026-07-31.

## 1. File inventory (one-line role, file:line for the key symbol)

Top-level `src/compiler/70.backend/linker/`:

- `link.spl:123,516` — `struct Linker` + `fn link()`: an older, self-described
  "main linker orchestration" (SMF load → type unify → ObjTaker specialize →
  mold native emit). **Not called by the live pipeline** — only its
  `LinkConfig` type is imported by `mold.spl:19` and `msvc.spl:7`. Dead
  orchestration, live type.
- `linker_wrapper.spl:22-25` — facade; re-exports
  `_LinkerWrapper/{native_all_support,archive_retention,native_linking,shared_linking}`.
  This is the real entry module used by the compiler driver.
- `_LinkerWrapper/native_linking.spl` — the live entry point.
  `link_to_native:161` dispatches by input kind; `link_native_unix:196` drives
  the direct mold/lld/ld path; `link_smf_bundle:417` is the SMF-aware path
  (extracts/lowers SMF → native objects, still finishes via `link_to_native`
  → `link_native_unix`/`link_native_cc`); `link_native_cc:617` is the `cc`
  fallback (this is the path actually exercised by §5's harness run).
- `linker_wrapper_helpers.spl` — `link_to_smf:44` (raw SMF passthrough writer),
  `link_to_self_contained:64` (SMF-in-ELF trailer format, magic `"SMFE"`),
  `build_trailer:222`, `fnv1a_hash:246`.
- `linker_wrapper_lib_support.spl` — library-aware linking:
  `scan_libraries_with_provider:47`, `resolve_symbols_from_libraries:133`,
  `extract_undefined_symbols:243`, `link_with_libraries:304`,
  `extract_objects_from_resolved:409`. **Single-pass**: one
  undefined-symbol scan → one library resolve → one extraction round, then
  hands off to `link_to_native`. No archive-fixpoint loop (see §6).
- `obj_taker.spl` (770 lines) — `struct ObjTaker:142`,
  `me objtaker_take_object:234` (per-symbol SMF extraction +
  template/generic instantiation via link-time monomorphization),
  `objtaker_infer_type_args:463`, `template_substitute:503`. This is the
  closest existing analogue to L1 decode + L4 select combined with
  link-time codegen (a responsibility the frozen contract does not carve out
  as its own stage).
- `lazy_instantiator.spl` — `struct LazyInstantiator:83`,
  `lazyinstantiator_new:102`; drives cross-module generic instantiation
  invoked from `ObjTaker`/`link.spl`.
- `archive_parser.spl` — `.a` (ar) format reader: `ar_parse:255`,
  `ar_parse_header:223`, `ar_parse_symbol_index:351`, `ar_find_member:328`.
  Pure decode; no fixpoint driver lives here (see `linker_wrapper_lib_support`
  above).
- `smf_header.spl:57,98` / `smf_enums.spl` — SMF header struct + `Platform`,
  `Arch`, `CompressionType`, `SmfAppType` wire enums (u8 discriminants,
  matches the frozen `structural/wire.spl` conventions in spirit though not
  literally reused).
- `smf_writer.spl` — `class SmfWriter:165` + `SmfSection:154`,
  `SmfWriterSymbol:137`, `SmfRelocation:148`; the live SMF **output assembly**
  writer used when compiling a single `.spl` to `.smf` (not the multi-input
  linker).
- `smf_reader.spl:186` `struct SmfReaderImpl`, `smf_reader_memory.spl` (facade
  over `_SmfReaderMemory/{header_parser,symbol_parser}.spl`) — SMF decode
  (L1) for both link-time and load-time (module loader) consumers.
- `lib_smf.spl:47,176` `LibSmfHeader`/`ModuleIndexEntry` — `.lsm` archive
  format (SMF-native library container, magic constant `LSMF_MAGIC`).
  `lib_smf_writer.spl:40` `LibSmfBuilder` / `lib_smf_reader.spl:26`
  `LibSmfReader` build and read it.
- `object_provider.spl:21,111` `struct ObjectProvider` — unified module
  lookup (SMF direct file, `.lsm` archive member, or native `.a`/`.o`),
  used by `link_with_libraries`.
- `smf_getter.spl:84,90` `struct SmfGetter` — search-path-based module
  discovery (`add_search_path:109`, `scan_search_paths:169`,
  `search_for_module:361`). This is the closest thing to L0 discover.
- `crt_discovery.spl:23` `find_crt_files` — discovers `crt1.o`/`crti.o`/
  `crtbegin.o`/dynamic linker/lib dirs for the direct-linker path.
- `reloc_engine.spl` — self-contained x86_64/aarch64/riscv relocation
  formula engine (`reloc_apply_x86_64:135`, `reloc_apply_aarch64:166`,
  `reloc_apply_riscv:189`, dispatch `reloc_apply:216`). **Dead**: only
  referenced by `__init__.spl`'s re-export; grep of `src/compiler` finds no
  other caller. The live pipeline's relocation is done by the external
  `mold`/`lld`/`ld`/`cc` process, not this file.
- `sym_resolver.spl` — ELF-shaped symbol resolution (`SymEntry:22`,
  `sym_resolve_objects:143`, strong/weak binding rules at `is_strong:60`/
  `is_weak:65`). **Dead** in the same sense as `reloc_engine.spl` — only
  self-referenced via `__init__.spl`.
- `symbol_analysis.spl` — `SymbolGraph`/`SymbolAnalyzer`
  (`analyze_reachability:90`, `find_dead_symbols:115`). **Dead**: no caller
  outside `__init__.spl` and its own spec. Reachability/dead-strip in the
  live pipeline is instead the external linker's `--gc-sections`/
  `-dead_strip` flag (`_LinkerWrapper/native_linking.spl:281,285`), not this
  module.
- `object_resolver.spl:24,212` `ObjectFileResolver`,
  `resolve_objects_for_modules:190` — imported by
  `linker_wrapper_lib_support.spl:11` but never called there (0 call-site
  matches); `mod.spl:29` marks it `# Compiled-only` and comments the export
  out. Effectively unwired.
- `object_emitter.spl:9` `assemble_code_units` — turns `ObjectCodeUnit`s into
  a real `.o` via `objcopy`/`llvm-objcopy` (`try_objcopy:49`,
  `try_llvm_objcopy:60`); used by both `native_linking.spl` and
  `object_provider.spl` (99.loader side) — this is a real, live L9-adjacent
  step, but it's producing native ELF object files, not SMF output bytes.
- `elf_parser.spl`, `elf_inspect.spl`, `macho_parser.spl`, `macho_inspect.spl`,
  `pe_parser.spl`, `pe_inspect.spl`, `msvc.spl`, `mold.spl`, `wasm_linker.spl`
  — format-specific readers/wrappers for the platforms the direct-linker path
  supports; `mold.spl:514` has its own `fn link()` used by
  `_link_native_mingw`/`shared_linking.spl` call sites, separate from
  `link.spl`'s and `linker_wrapper`'s `link`.
- `swa.spl`, `swa_reader.spl`, `swa_writer.spl`, `swa_zip*.spl` — a separate
  "SWA" (standalone web app?) zip-based bundle format, unrelated to SMF
  linking proper; out of scope for this map beyond noting it lives in the
  same directory.
- `linker_context.spl:16` `LinkerCompilationContext(CompilationContext)` —
  small context/config carrier for the legacy `link.spl` pipeline.
- `platform_defaults.spl`, `mold_compatibility.spl`, `link_deps.spl`,
  `linker_script.spl` — platform default flag tables, mold-vs-lld
  compatibility shims, and a `check_links`/`resolve_link_deps` consumer used
  by `src/app/cli/check_links.spl:6` (separate from the main link path — a
  static "do these modules resolve" checker, not an emitter).
- `elf_writer.spl` (10 lines) — stub/facade only.
- `lld_sffi.spl`, `lld_shim.cpp/.h` — in-process LLD FFI bridge, used on the
  SimpleOS target (`is_simpleos_target()` branch,
  `_LinkerWrapper/native_linking.spl:388-398`) where fork/exec isn't
  available.

## 2. Invocation path (CLI → stage → linker entry)

Two live paths exist; both bottom out in the same `linker_wrapper` facade:

1. **`bin/simple native-build --entry <f> -o <out> --entry-closure
   --runtime-bundle auto`** (verified live, §5) → `src/app/cli/native_build_main.spl:341`
   `main()` self-re-execs the compiler binary as a build worker → the driver
   compiles each module to SMF, then calls the native-output path below.
2. **`bin/simple build` / in-process driver AOT path**:
   `CompilerDriver.compile_to_native` —
   `src/compiler/80.driver/driver_aot_native_output.spl:234` — imports
   `link_to_native`, `NativeLinkConfig` from `linker_wrapper` (same file,
   line 8-12), called from
   `src/compiler/80.driver/driver_aot_pipeline.spl:120,145`.
3. Older/parallel entry: `src/compiler/70.backend/build_native.spl:156-157`
   and `build_native_pipeline.spl:170-171` construct
   `BuildLinker.new(link_config)` (`src/compiler/70.backend/build_native_types.spl:47-79`
   `struct BuildLinker` / `me link`) which itself just calls
   `build_link_native` (`build_native_types.spl:81`) →
   `lw_link_to_native` = `linker_wrapper.link_to_native` (same function as
   above, aliased on import at `build_native_types.spl:10`).

All three converge on
`_LinkerWrapper/native_linking.spl:161 fn link_to_native(object_files, output,
config: NativeLinkConfig)`, which then branches: SMF inputs →
`link_smf_bundle:417`; else direct linker → `link_native_unix:196`; else `cc`
fallback → `link_native_cc:617` (this is the branch the verified harness in
§5 actually took).

## 3. Stage-mapping table (L0–L12 → existing owner)

| Stage | Contract responsibility | Existing owner today | Notes |
|---|---|---|---|
| L0 discover | find SMF/archive inputs | `smf_getter.spl:84,90,109,169,361` `SmfGetter`; `linker_wrapper_lib_support.spl:47` `scan_libraries_with_provider` | Search-path scan, not snapshot/EntityRef-based |
| L1 decode | parse SMF header/symbols/sections | `smf_header.spl:98` `impl SmfHeader`; `smf_reader.spl:186,196` `SmfReaderImpl`; `_SmfReaderMemory/{header_parser,symbol_parser}.spl` | u8 discriminant enums (`smf_enums.spl`), no `Hash128`/`EntityRef` identity |
| L2 arenas | resident symbol/section/reloc arenas | **no current equivalent** | Everything is Simple arrays/structs (`[SmfWriterSymbol]`, `[SmfRelocation]` in `smf_writer.spl:167-169`); no `placement_contracts` resident-tier arena usage found in this dir |
| L3 intern/sort | name interning + stable ordering | **no current equivalent** | No hash-intern table; `smf_writer.spl:171` `string_offsets: {text: i64}` is a plain dict, not a stable-sorted key structure |
| L4 select | pick winning definition per key | `obj_taker.spl:234` `objtaker_take_object` (per-symbol, on demand, not batch-grouped); duplicate handling is `--allow-multiple-definition` at the external-linker level (`native_linking.spl:66,80,112-114`), **not** an in-repo `DuplicateDefinition` diagnostic |
| L5 archive fixpoint | iterate archive extraction to closure | **no current equivalent (single-pass only)** | `linker_wrapper_lib_support.spl:304` `link_with_libraries` does exactly one undefined-symbol-scan → one resolve → one extract round, then delegates to the external linker for any further pulls |
| L6 reachability | dead-strip / mark-reachable | **dead in-repo code**: `symbol_analysis.spl:65-141` `SymbolGraph.analyze_reachability`, `find_dead_symbols:115` — zero external callers. Live behavior comes from `--gc-sections`/`-dead_strip` flags to the external linker (`native_linking.spl:281,285`) |
| L7 address layout | assign addresses/output ranges | delegated to external `mold`/`lld`/`ld`/`cc` in the live path; `smf_writer.spl:137-146` has `layout_phase`/`layout_pinned`/`is_event_loop_anchor` fields suggesting an intended in-house layout scheme, but no driver assembles multi-object layout from them today |
| L8 relocation | apply relocation formulas | **dead in-repo code**: `reloc_engine.spl:135,166,189,216` (`reloc_apply_x86_64/aarch64/riscv`, dispatch `reloc_apply`) — zero callers found; live relocation happens inside the external `mold`/`lld`/`ld`/`cc` process |
| L9 output assembly | assemble output bytes | `smf_writer.spl:165` `SmfWriter` (single-module SMF emission) for the compile-to-SMF path; `object_emitter.spl:9` `assemble_code_units` (objcopy-based) for extracted-object materialization; final native byte assembly is the external linker's job |
| L10 provenance | input→output byte-range mapping | **no current equivalent** — no `provenance`/`MappingGraph`-shaped code found anywhere under this directory |
| L11 SSD write | staged/direct output write | plain `rt_file_write_text`/file-copy calls (e.g. `linker_wrapper_helpers.spl:328,368,384` `write_elf_bytes_to_file`/`write_bytes_to_file`/`append_bytes_to_file`) — synchronous whole-file writes, no staged/direct distinction |
| L12 manifest commit | commit output + receipts | **no current equivalent** — no `StageReceipt`/manifest-commit code in this directory |

## 4. Data structures → frozen record shapes

Current symbol shape closest to the contract's `DefinitionRecord`/
`ReferenceRecord` is `SmfWriterSymbol` (`smf_writer.spl:137-146`):

```
struct SmfWriterSymbol:
    name: text
    binding: SmfWriterSymbolBinding      # Local | Global | Weak
    sym_type: SmfWriterSymbolType        # NoType | Function | Object | Section
    section_index: i64
    value: i64
    size: i64
    layout_phase: i64        # 0=startup,1=first_frame,2=steady,3=cold
    is_event_loop_anchor: bool
    layout_pinned: bool
```

and `SmfRelocation` (`smf_writer.spl:148-152`):

```
struct SmfRelocation:
    offset: i64
    symbol_index: i64
    reloc_type: RelocationType   # Abs64|Rel32|PltRel32|GotRel32|Abs32
    addend: i64
```

Mapping onto the frozen v1 wire records (§3 of the contract):

- `name: text` → today's identity, would become `ResolveKey.name_hash: Hash128`
  (interned) + `space: u32`; there is no interning today (L3 gap above).
- `binding` (Local/Global/Weak) + `sym_type` (NoType/Function/Object/Section)
  → both need to fold into `DefinitionRecord.attributes: u64`, since the
  frozen record has no separate binding/type fields. This is exactly the
  "`SmfLinkProfile` record `attributes` bit assignments" the contract
  defers to the L1-decode wave (contract §6, item 2).
- `layout_phase: i64` (0-3) → maps directly to the frozen `link.*` tag name
  `hot_order` (contract §4) — an attribute bit range, not a separate field.
- `is_event_loop_anchor: bool`, `layout_pinned: bool` → **not** covered by
  the frozen `link.*` tag list (`symbol.{binding,visibility,resolution}`,
  `section.{kind,alignment}`, `relocation.kind`, `reachable`,
  `icf.candidate`, `hot_order`, `output_range`). These two existing bits
  need either a new tag name or dedicated `attributes` bits before
  `SmfLinkProfile` can losslessly round-trip current `SmfWriter` output —
  flag for the L1-decode attribute-bit freeze.
- `RelocationType` (5 variants: Abs64, Rel32, PltRel32, GotRel32, Abs32) is
  a strict subset of what `reloc_engine.spl`'s dead code already models
  (arch-specific reloc type numbers per `RelocArch`, `reloc_engine.spl:49`)
  — the frozen `relocation.kind` tag needs at least these 5 plus whatever
  `reloc_engine.spl`'s x86_64/aarch64/riscv formulas assume (it uses raw ELF
  reloc-type integers, not this closed enum).
- `section_index: i64` / target section → `owner: EntityRef` in the frozen
  record; today it's a bare array index into `SmfWriter.sections`
  (`smf_writer.spl:167`), not a stable cross-snapshot identity.
- Duplicate-definition and resolution status: today there is no
  `ResolveStatus`/`ResolveReason`-shaped result anywhere in this directory —
  duplicates are suppressed at the external-linker-flag level
  (`--allow-multiple-definition`, §3 above), so `ResolveReason.DuplicateDefinition`
  has no producer to migrate from; it will be new behavior, not a port.

## 5. Byte-parity harness (verified 2026-07-31)

Command (run twice, output hashed both times):

```
bin/simple native-build --entry examples/01_getting_started/hello_native.spl \
    -o <out> --entry-closure --runtime-bundle auto
```

Fixture used: `examples/01_getting_started/hello_native.spl` (in-tree,
3 lines, `print "Hello World"`) — chosen because it's the smallest existing
fixture whose header comment names this exact command
(`examples/01_getting_started/hello_native.spl:2`), and because
`bin/simple compile --format=smf -o out.smf <same file>` **crashed**
(`runtime error: field access on nil receiver`, exit 132, "dumped core") —
so `compile --format=smf` is not usable as the harness command today; see §6.

Observed, from an actual run (not simulated):

```
$ bin/simple native-build --entry examples/01_getting_started/hello_native.spl \
    -o hello_run1 --entry-closure --runtime-bundle auto
Generating 2 stub functions for unresolved symbols...
Unresolved symbol preview: __cpu_indicator_init, __cpu_model
Linked: .../hello_run1 (22 KB) via clang
Build complete: 1 compiled, 0 cached, 0 failed
exit=0
```

Run twice into `hello_run1` / `hello_run2`:

```
sha256sum hello_run1 hello_run2
b9f37a50a84d2d6601c98b9e8ac3ddce814d7cfb275a5aa7683f416e9bc86121  hello_run1
b9f37a50a84d2d6601c98b9e8ac3ddce814d7cfb275a5aa7683f416e9bc86121  hello_run2
cmp hello_run1 hello_run2   # → identical, no output (exit 0)
```

Both files: 23384 bytes, exit code 0 both runs, byte-identical
(sha256 `b9f37a50a84d2d6601c98b9e8ac3ddce814d7cfb275a5aa7683f416e9bc86121`).

**Caveat for Phase 1**: the log line `"via clang"` proves this run took the
`link_native_cc` fallback (`_LinkerWrapper/native_linking.spl:617`), not the
direct `mold`/`lld` path (`link_native_unix:196`) and not a pure SMF→SMF
output (`link_to_smf`, `linker_wrapper_helpers.spl:44`). It exercises SMF
decode + `ObjTaker` extraction (L1/L4-ish) faithfully, but L7/L8/L9 in this
run are performed by the external `clang` process, not by any Simple code in
this directory. Phase 1's "byte-identical to current SMF linker" acceptance
bar should hook its comparison at the `link_smf_bundle` boundary
(`native_linking.spl:417`, output = the materialized `.o` set from
`objtaker_take_object` + `assemble_code_units`) if the goal is to compare
Simple-owned bytes, or at the final binary (as done here) if the goal is
end-to-end user-visible parity — these are two different comparison points
and should not be conflated.

## 6. Risks / oddities

1. **`compile --format=smf` crashes on the smallest in-tree fixture.**
   `bin/simple compile --format=smf -o out.smf examples/01_getting_started/hello_native.spl`
   → `runtime error: field access on nil receiver`, SIGILL-class abort (exit
   132, `timeout: the monitored command dumped core`). Entry point:
   `src/app/cli/bootstrap_main.spl:318` `run_compile_bootstrap`. This means
   the *simplest* possible SMF-output harness command is currently broken;
   `native-build` (§5) was needed instead. Worth filing as its own bug —
   not diagnosed further here per lane scope (read-only).
2. **Three separate, only-partially-overlapping "link" entry points** exist
   in this directory: `link.spl:516 fn link()` (dead, SMF→native, type-only
   import survives), `mold.spl:514 fn link()` (used by mingw/shared paths),
   and `linker_wrapper`'s `link_to_native`/`link_to_smf`/
   `link_to_self_contained` (the live one). A reader grepping for "the
   linker" will find the wrong one first (`link.spl` is alphabetically
   prominent and has the most complete-looking doc comment).
3. **L5/L6/L7/L8 are structurally absent from the Simple-owned code path in
   production use** — archive fixpoint, reachability, address layout and
   relocation are all delegated to the external `mold`/`lld`/`ld`/`cc`
   binary via CLI flags (`--gc-sections`, `-dead_strip`, `--icf=all`,
   `--allow-multiple-definition`, dynamic linker/CRT wiring in
   `crt_discovery.spl`). The Simple-language implementations that *look*
   like they'd own these stages (`symbol_analysis.spl`, `reloc_engine.spl`,
   `object_resolver.spl`) are unwired dead code with zero external callers
   (verified via grep for their public symbols across `src/compiler`). Any
   Phase-1 claim of "byte-identical to current SMF linker" must be explicit
   about which of these two things is being compared — GraphResolveCore's
   in-house L5-L8 vs. today's external-tool delegation are not replacing
   like-for-like, they're replacing "not implemented in Simple at all."
4. **Determinism risk — debug builds only.** The verified §5 run used
   `config.debug = false` and produced byte-identical output across two
   runs despite each run using a fresh randomized `mktemp -d
   /tmp/simple_link_XXXXXX` directory (`mold.spl:685,704`). If `debug: true`
   is set, `-g` is passed to the external linker (`native_linking.spl:376-377`);
   DWARF `DW_AT_comp_dir`/`DW_AT_name` can embed that randomized absolute
   temp path, which would break byte parity for debug builds even though
   this scout's non-debug run was clean. Not exercised here — flag for
   Phase-1 fixture selection (use `debug: false` fixtures for byte-parity
   gating, or normalize `comp_dir`).
5. **`--build-id` is content-hashed, not timestamp-based**
   (`native_linking.spl:269`, GNU `ld`/`mold`/`lld` default SHA1-of-content
   build-id), so it did not threaten this run's determinism — but it is an
   external-tool default this repo does not control or pin, and future
   linker upgrades could change the algorithm.
6. **Duplicate-symbol policy inversion vs. the frozen contract.** The
   contract's `ResolveReason.DuplicateDefinition` (contract §3) implies
   duplicates are detected and diagnosed. Today's default
   (`NativeLinkConfig.allow_duplicate_definitions: true`,
   `native_linking.spl:80`) actively *suppresses* the external linker's
   duplicate-symbol error via `--allow-multiple-definition`
   (`unresolved_symbol_flags_for_unix_linker:112-114`). A faithful
   `SmfLinkProfile` port needs an explicit decision on whether to preserve
   this permissive default or tighten to match the contract's diagnosed
   `DuplicateDefinition` path — silently doing the latter would be a
   behavior change, not a port.
7. **`mod.spl:29` comments out the `object_resolver` export** with the note
   "Compiled-only: object file resolution" — a bootstrap-parser-vs-native
   divergence marker consistent with other known seed/self-hosted gaps in
   this repo; the file is otherwise a complete, spec-tested implementation
   that nothing in the live path calls.
8. **`swa*.spl` files share the linker directory** but implement an
   unrelated zip-based bundle format ("SWA") — not SMF, not in scope for
   this contract, but a reader enumerating the directory for "the SMF
   linker" will trip over 5 files (`swa.spl`, `swa_reader.spl`,
   `swa_writer.spl`, `swa_zip.spl`, `swa_zip_reader.spl`) that are not part
   of it.

## References

- Contract: `doc/05_design/platform/structural_compute/link_manager_contract_v1.md`
- Plan: `doc/03_plan/platform/structural_compute/link_manager_plan.md`
- Lane guide: `.spipe/link_manager/LANE_GUIDE.md` § "Lane SMFMAP"
