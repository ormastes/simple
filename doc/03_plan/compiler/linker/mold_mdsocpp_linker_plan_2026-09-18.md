# mold-based MDSOC++ Linker — Plan (2026-09-18)

**Status:** RC1 lanes A0/A1/A2/A4a/A5 started 2026-09-18. **Design:** `doc/05_design/compiler/linker/mold_mdsocpp_linker_design.md` (D1–D9, §2 owner map).
**Research/audit:** `doc/01_research/compiler/linker/{mold_mdsocpp_linker_2026-09-15,linker_loader_inventory_2026-09-18}.md`.
**Base:** `simple-rc1-share` @ `cc205ae0778`. **Host for evidence:** aarch64, `bin/release/aarch64-unknown-linux-gnu/simple`.
`L/` = `src/compiler/70.backend/linker/`, `LD/` = `src/compiler/99.loader/`, `T/` = `test/01_unit/`.

## 1. Rules every lane follows

| Rule | Concretely |
|---|---|
| Evidence command | `B=$(readlink -f /home/yoon/dev/simple/bin/simple); $B test --no-session-daemon <one spec>` — one spec per run; bracket every measurement with `readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"` |
| TDD | The lane's first commit is a **red** spec under `T/` naming the behaviour; the second turns it green. Red→green output is pasted in the PR body. No spec may be skipped or tagged away without approval |
| Exclusive ownership | Only the `Owns` column may be edited; anything else is a handoff to the owning lane (KPF fabric coordination contract). Two lanes never touch one file |
| Duplicate test trees | If `test/unit/<same relative dir>` exists (it does for `compiler/backend/linker/`, 8 files, and `os/memory/`), add the **identical** spec to both trees — a spec in one tree only is a "mirror-only" offender and hard-blocks the push. New unmirrored dirs (`T/lib/common/linker/`, `T/compiler/loader/`) go in `test/01_unit/` only. Before pushing run `sh scripts/check/check-test-tree-divergence-delta.shs <origin/main sha> <tip>` and record the pre-existing offender list in the PR |
| Direct-rt ratchet | `sh scripts/check/check-no-direct-rt.shs --roots src` count must not rise; SOSIX leaves are requested from the SOSIX plan, never added here |
| Fable review before landing | A higher-capability reviewer reads the full `src/` diff plus the red→green transcript for every lane before push (user rule). Small-model lanes are marked `haiku-ok`; everything else `sonnet`/`opus` |
| Landing | `work/<topic>` branch → PR → `gh pr merge --merge` (main is ruleset-protected). Baseline-file changes are their own commit stating the measured count |
| Board-runnable | Anything exercised on QEMU (lane A9) keeps a documented board build+boot+run path or files a board-blocked record |
| Reports | Measurement outputs are **not** committed unless asked; recipes (`.shs`) are |

## 2. RC1 eligibility

| RC1-eligible (zero behaviour change) | Post-RC1 |
|---|---|
| Deleting dead code with 0 non-spec importers (design §3 wave 0) | Internal ELF/SMF engines, archive fixpoint, GC, exec writer |
| Contracts in `src/lib/common/linker/` + their specs | Loader relocation convergence (turns silent truncation into an error) |
| Adapter `LinkRequestV1` → existing `link_to_native` with byte-identical argv; receipts naming the external engine | Bounded mode, 6 GB accounting, compositions |
| `SIMPLE_LINKER=internal` → named `UnsupportedFeature` error | Boot layout, COFF, Mach-O, FreeBSD, RISC-V, Windows ARM64 |
| Tests, goldens, census scripts, doc amendments | Flipping `mold_is_pure_simple_linker_complete` |

## 3. Gates (dependencies, not dates)

| Gate | Work (lanes) | Exit criterion (fail-closed) |
|---|---|---|
| **G0** RC1 | Dedup/delete wave 0 (A1); baseline corpus + relocation census (A5); freeze 6 GB meaning + accounting classes and amend the 9 contradicted docs (A0); re-verify importer counts on the landing sha | `git grep` importer count 0 for every deleted path; census artifact lists the real `R_*` set per arch for native-backend and LLVM objects; all 8 `T/compiler/backend/linker/*_spec.spl`, all 8 `T/compiler/linker/gpu_smf/*_spec.spl` and `T/lib/mdsocpp/seal_spec.spl` green on the aarch64 host |
| **G1** RC1 | `Link*V1` contracts (A2); external-engine adapter + receipts (A3); reloc oracle unification in dead code (A4a) | argv golden byte-identical before/after for Linux x86_64/aarch64, macOS, FreeBSD, Windows arg builders; hello-world links and runs on the aarch64 host through the adapter; `SIMPLE_LINKER=internal` fails with `UnsupportedFeature`; `LinkReceiptV1.engine` names `mold`/`ld.lld`/`ld`/`cc`/`link.exe` |
| **G2** post | SMF engine driver L2–L8 with receipts (A6); loader convergence (A4b); SMF read dedup (A12); ELF slice 1 static ET_EXEC (A7) then slice 2 LLVM corpus | slice 1: native-backend hello-world links **internally** and runs on aarch64 and x86_64; slice 2: the real compiler links internally, `llvm-readelf -l -S -r` parity with `ld.lld` output, execution corpus identical; direct-vs-external time measured and reported with binary identity |
| **G3** post | Bounded-stream then bounded-spill (A8); accounting; SOSIX H10–H12 landed in the SOSIX plan | full compiler links under a measured `QualifiedJobScope` peak < 6,000,000,000 bytes with semantics unchanged (fast/bounded output digest parity); `MeasuredOnly` never closes this gate |
| **G4** post | BootLayoutPlan (A9); COFF / Mach-O / FreeBSD / RISC-V (A10) | per platform: native run or real-firmware boot **and** board evidence (or board-blocked record); PHDR/section parity vs `ld.lld -T` |
| **G5** post | Dynamic aspect packs, generation-safe replacement; static recovery composition keeps bootstrap non-circular | add/replace capsule without kernel edits; old sessions unaffected; `simple --help` loads no linker code |
| **G6** post | Per-platform cutover; completion gate flip (A13); SIMD/GPU/caches behind own gates | receipts name the internal engine on every cut-over platform; `mold_is_pure_simple_linker_complete()` returns `true` only then |

## 4. Lanes (exclusive ownership)

`Start` = can begin immediately in parallel. Evidence column is the single spec run with the §1 command.

| Lane | RC1 | Owns (exclusive) | Deps | Work | Red spec first → evidence | Model |
|---|---|---|---|---|---|---|
| **A0** arch/integration | yes | this plan + design; `doc/03_plan/platform/structural_compute/link_manager_plan.md`; `doc/05_design/compiler/architecture/{mold_mimalloc_compatibility_surface,linker_script_gen_design}.md`; `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`; `doc/03_plan/os/in_guest_lld_link_ladder.md`; `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`; `doc/03_plan/agent_tasks/kernel_plugin_fabric.md` (ledger row only); `.spipe/link_manager/state.md`; new `doc/08_tracking/todo/linker_handoffs_2026-09-18.md`; `doc/00_llm_process/layer_expert/compiler/skill.md` | none | Apply design §10 amendments; file the S1 schema handoff and the SOSIX H10–H12 request as **handoff records** (the SOSIX plan file is owned by its own active lanes and is not edited here) | doc-only: `sh scripts/check/check-workspace-root-guard.shs` + doc-dir ≤10 rule | sonnet · **Start** |
| **A1** delete wave 0 | yes | `LD/{generation_sweeper,mod,module_loader_lib_support,resource_lifecycle,smf_cache_manager}.spl`; `LD/loader/{module_loader,smf_cache,arch_validator}.spl`; `L/{object_provider_adapter,smf_source,mod,__init__,linker_context,lazy_instantiator,wasm_linker,elf_inspect}.spl`; `L/mold.spl` dead fns only (`mold_post_link_check`, `write_elf_object`, `parse_linker_diagnostics`, `mold_find_crt_files`) | none | Delete; fold `elf_inspect` uses into `elf_parser`; re-grep importers on the landing sha | red: `T/compiler/backend/linker/linker_dead_imports_spec.spl` asserting no `src/` file imports a deleted module (fails while `mold.spl:16` imports `elf_inspect`) → green; then `elf_parser_spec`, `reloc_engine_spec` unchanged green | haiku-ok · **Start** |
| **A2** contracts | yes | new `src/lib/common/linker/{link_request_v1,link_policy_v1,link_receipt_v1,__init__}.spl`; `T/lib/common/linker/*_spec.spl` | none | Design §6.2 structs with `KpfSchemaHeaderV1`; total decoders; outcome enum; hand-derived goldens | red: `T/lib/common/linker/link_request_v1_spec.spl` (header validation via `kpf_validate_schema_header_v1`, unknown mode rejected, policy `mode=Bounded` requires `job_memory_limit_bytes > 0`) → green | sonnet · **Start** |
| **A3** external engine adapter | yes | `L/mold.spl` (`find_linker_path`, `requested_linker_override`); new `L/link_engine_external.spl` (`link_request_to_native(req, policy)` projects to `NativeLinkConfig` and calls `link_to_native` through the `linker_wrapper` facade — `native_linking.spl` is **not** edited); `T/compiler/backend/linker/link_engine_external_spec.spl` (+ `test/unit/` mirror) | A2 | Zero behaviour change: argv builders untouched; receipt filled from `find_linker_path` result; `internal` alias → `UnsupportedFeature` | red: golden at the `NativeLinkConfig` projection level (field-for-field equality with a hand-built config for Linux x86_64/aarch64, macOS, FreeBSD, Windows rows — argv depends on host probes and is covered by one real link); `SIMPLE_LINKER=internal` must return the named error → green; then hello-world `simple build` on the aarch64 host runs | sonnet |
| **A4a** reloc oracle (dead code) | yes | `L/reloc_engine.spl`; `L/gpu_smf/smf_reloc_formulas.spl` (wire-4 golden only); `T/compiler/backend/linker/reloc_engine_spec.spl` (+ `test/unit/` mirror); `T/compiler/linker/gpu_smf/smf_reloc_formulas_spec.spl`; new `T/compiler/loader/loader_reloc_wire4_spec.spl` | none | `reloc_engine` computes S+A / S+A-P via `smf_reloc_compute`, **rejects** instead of masking (`:150`); add aarch64 `ADR_PREL_PG_HI21`/`ADD_ABS_LO12_NC`/`LDST64_ABS_LO12_NC` field encoders and RISC-V hi/lo pairing; precondition: read `smf_elf_parser.spl:239-246` mapping table and pin wire 4 = `G + A − P` (S = GOT-entry address, design §4) | red: `reloc_engine_spec` "R_X86_64_32 out of range rejects" (currently masks) and "ADR_PREL_PG_HI21 encodes page delta" (currently unhandled) → green; `loader_reloc_wire4_spec` proves the live loader formula for wire 4 yields the symbol's bytes, not its address (stays red until A4b, tagged `@tag:in-development`) | sonnet · **Start** |
| **A4b** loader convergence | no | `LD/module_loader_compat.spl` (relocation block `:1324-1370` only); `os/smf/smf_dynlib.spl` (`smf_dynlib_apply_relocation` only); `LD/loader/object_mapper.spl`; `T/compiler/loader/loader_reloc_oracle_spec.spl` | A4a | Both live loops compute via `smf_reloc_compute_wire`, write via `native_reloc_write_*`; synthesize a per-module GOT for wire 4; delete `apply_smf_relocations`; document the truncation → error change | red: spec proving loader type-2 with delta > 2^31 currently truncates silently (as-is behaviour pinned first), then expects `LoadResult.Error` → green; A4a's `loader_reloc_wire4_spec` turns green; `bin/simple run` hello-world SMF still runs | sonnet |
| **A5** corpus + census | yes | new `scripts/check/check-link-corpus-baseline.shs`; `test/fixtures/linker/corpus/*.sdn` (recipes, not binaries); `T/compiler/backend/linker/link_corpus_recipe_spec.spl` | none | Recipes for: small CLI, full compiler release, compiler+providers, full-debug, SimpleOS kernels (6 `linker.ld`), giant-object set; `llvm-readelf -r` census per arch and per producer (native backend vs LLVM); fail-closed `--selftest` (0 objects = ERROR) | red: recipe spec asserts every corpus row names inputs + expected outcome and that the census script emits a verdict line → green; run census on the aarch64 host and paste the `R_AARCH64_*` set into the PR | haiku-ok · **Start** |
| **A6** SMF engine driver | no | `L/gpu_smf/**` except `smf_reloc_formulas.spl`; new `L/gpu_smf/smf_link_driver.spl`; `T/compiler/linker/gpu_smf/smf_link_driver_spec.spl` | A2, A4a | `impl ResolveProfile for SmfLinkProfile`; one driver runs L2→L8 on CPU with a `StageReceipt` per stage keyed by `SMF_LINK_STAGE_L*`; takes over `.spipe/link_manager/state.md:178-182` | red: driver spec links two in-memory SMF modules with one cross reference, expects 7 receipts and a patched Rel32 → green; existing 8 gpu_smf specs unchanged | opus |
| **A7** ELF capsule slice 1/2 | no | `L/elf_parser.spl`; `L/_ElfWriter/**`; `backend/native/elf_writer.spl` (re-base onto codec only); `L/sym_resolver.spl`; `L/archive_parser.spl`; new `L/elf/{elf_exec_writer,archive_closure,reloc_scan,synthetic_sections}.spl`; `L/linker_wrapper_lib_support.spl`; `L/link.spl` (delete remainder); `T/compiler/backend/linker/elf_*_spec.spl` | A2, A4a, A5, A6 | Slice 1: static ET_EXEC + PHDRs from native-backend objects, archive fixpoint, GC roots, `internal` engine wired behind `find_linker_path`. Slice 2: GOT/PLT/`.dynamic`/TLS/`.eh_frame_hdr`/build-id for the LLVM corpus | red: `elf_exec_writer_spec` "two-object static exec has PT_LOAD RX+RW and entry = `_start`" → green; then `readelf` parity + run on aarch64 and x86_64; slice 2 red spec = compiler corpus link | opus |
| **A8** bounded + compositions | no | new `src/compositions/linker_{fast,bounded}/**`; new `src/lib/nogc_async_mut/link_working_set/**`; `L/link_accounting.spl`; `T/compiler/backend/linker/link_bounded_*_spec.spl`; `test/05_perf/compiler/linker/*` | A7, SOSIX H10–H12 | Two `CapsuleDescriptorV1` + `mdsocpp_seal_v1` with `memory_budget_bytes = 6_000_000_000`; windowed inputs, staged output, spill with checksums; `QualifiedJobScope` via cgroup v2; Auto mode records reasoning | red: seal spec "bounded composition over budget → `MemoryBudgetExceeded`"; perf spec "compiler corpus peak < 6e9 under QualifiedJobScope" (ERROR when class is MeasuredOnly) → green | opus |
| **A9** boot layout | no | new `L/boot_layout/**`; `L/linker_script.spl`; `src/app/linker_gen/**`; `baremetal/link_wrapper.spl`; `backend/simpleos_native_linkers.spl`; `T/compiler/backend/linker/boot_layout_*_spec.spl`; `scripts/check/check-boot-layout-parity.shs` | A7 | Parse PHDRS/AT/KEEP/NOLOAD/`. +=`/ALIGN/PROVIDE/ASSERT; `BootLayoutPlan`; rung ladder of design §9; external `-T` stays producer until board rung | red: `linker_script_spec` round-trips all 6 `src/os/kernel/arch/*/linker.ld` (fails today on `PHDRS`) → green; parity script verdict; real-firmware QEMU boot script; board transcript or board-blocked record | opus |
| **A10** COFF / Mach-O / FreeBSD / RISC-V | no | `L/pe_*.spl`, `L/macho_*.spl`, `backend/native/macho_writer.spl`, `L/msvc.spl`, new `L/{coff,macho}/**`, riscv rows of `L/reloc_engine.spl` by handoff from A4a | A7 | One capsule per format; external tool remains oracle; Windows ARM64 = new capability, not a regression fix | per platform red spec + native run on that OS; FreeBSD via `scripts/check/check-freebsd-bootstrap-qemu.shs --smoke` | opus |
| **A11** conformance / perf | no | `test/05_perf/compiler/linker/**`; `scripts/check/check-link-mutation-gates.shs`; `doc/10_metrics/compiler/linker/` recipes | A7 | Paired runs vs pinned mold/lld, cold and warm; mutation gates from research §11 (each mutation must turn its gate red) | red: mutation script `--selftest` with 9 mutations → green; 2 % regression = investigation | sonnet |
| **A12** SMF read dedup | no | `L/smf_reader.spl`; `L/obj_taker.spl`; `L/_SmfReaderMemory/**`; `L/smf_reader_memory.spl`; `T/compiler/backend/linker/smf_reader_*_spec.spl` | A1 | `smf_reader` becomes a file→`SmfReaderMemory` shim; pin `obj_taker` behaviour first | red: spec pins `objtaker_take_object` results on a fixture SMF before the swap → green after | sonnet |
| **A13** completion gate | no | `L/mold_compatibility.spl`; `test/01_unit/os/memory/mold_linker_spec.spl`; `test/unit/os/memory/mold_linker_spec.spl` | G6 | Flip `mold_is_pure_simple_linker_complete()` to a computed value (internal engine wired for ELF x86_64+aarch64 and receipts prove it); edit both mirrors identically | red: both specs updated to expect `true` fail until G6 → green | sonnet |

**Start now in parallel (no shared files, no deps): A0, A1, A2, A4a, A5.** A3 starts when A2's struct names land (can stub against the design table in the meantime in its own file only).

## 5. Ownership conflicts resolved up front

| File | Owner | Others |
|---|---|---|
| `L/mold.spl` | A3 (selection fns) · A1 (dead fns, deleted first) | A1 lands before A3 touches the file |
| `L/gpu_smf/smf_reloc_formulas.spl` | A4a | A6 owns the rest of `gpu_smf/` |
| `L/reloc_engine.spl` riscv rows | A4a | A10 requests by handoff |
| `L/elf_parser.spl` | A7 | A1 folds `elf_inspect` into it **before** A7 starts |
| `LD/module_loader_compat.spl` | A4b (reloc block only) | nobody else |
| `host_facade.spl` and any SOSIX file | SOSIX plan lanes | linker lanes never edit SOSIX; A0 files the H10–H12 request |
| `doc/03_plan/agent_tasks/kernel_plugin_fabric.md` | A0 (one ledger row) | S1 keeps `src/tool/kernel_plugin_schema/**` |

## 6. Completion gate (reused, not new)

`mold_is_pure_simple_linker_complete()` (`L/mold_compatibility.spl:109`) is the single completion predicate. It returns `true` only when all hold, each backed by a receipt from a real run:
1. `find_linker_path()` resolves `internal` on Linux x86_64 and aarch64 and the receipt names capsule `link_elf_fast`;
2. the full compiler corpus (A5 row "full compiler release") links internally and the execution corpus passes;
3. fast/bounded output digests match for the same request (G3);
4. SimpleOS x86_64 + arm64 kernels boot from `BootLayoutPlan` output on real firmware and a board (or a dated board-blocked record exists) (G4).
COFF/Mach-O completion extend `mold_compatibility_features` rows; they do not gate the predicate. Both `mold_linker_spec.spl` mirrors flip in the same commit (A13).

## 7. Blocked / external dependencies

| Item | Owner | Effect if missing |
|---|---|---|
| SOSIX mmap windows, worker pool, memory limit (H10–H12) | `doc/03_plan/runtime/sosix_host_interface_only_plan_2026-09-18.md` | A8 cannot close G3; A7 fast path stays single-threaded (`max_workers = 1` in receipt) |
| S1 schema handoff for `Link*V1` | KPF fabric S1 owner | contracts stay plain structs (design D8); no generated C/Rust bindings |
| Seed deploy after PR #388 (`rt_fd_pread` externs) | bootstrap owners | `posix_spec` red on the deployed seed; bounded `pread` windows untestable on `bin/release` until then |
| Board access for arm64/x86_64 kernels | hardware | A9 rung 4 files a board-blocked record; QEMU-only is not completion |
| macOS / Windows / FreeBSD hosts | CI | A10 rows stay `NotCertified` with external oracle |

## 8. Open questions (mirror of design §12)

1. Slice-1 target: static ET_EXEC over native-backend objects first, or the LLVM/dynamic corpus directly?
2. `Link*V1` as plain structs outside the S1 generator until a handoff?
3. Kernel loader twins with golden parity instead of a shared codec?
4. Retire `lld_sffi`/`lld_shim.cpp` before the internal engine owns SimpleOS (error-message-only change)?

**Decided 2026-09-18:** (1) slice 1 = static ET_EXEC over native-backend objects; (2) `Link*V1` plain structs until S1 handoff; (3) kernel loader twins stay separate with golden parity; (4) `lld_sffi`/`lld_shim` retirement deferred to post-RC1 (not in any RC1 lane).

## 9. RC1 lane status — 2026-09-18 (merged into `work/rc1-dataframe-sosix`)

| Lane | Result | Evidence |
|---|---|---|
| A0 | **pass** (Fable) | 9 contradicted docs amended; decisions recorded; handoffs `doc/08_tracking/todo/linker_handoffs_2026-09-18.md` |
| A1 | **pass** (Fable) | 11 dead files deleted; `linker_dead_imports_spec` 9/9 (5/9 red before). **Kept**, because the audit was wrong about their callers: `loader/module_loader.spl`, `loader/smf_cache.spl`, `linker_context.spl`, `lazy_instantiator.spl`, `elf_inspect.spl`, mold `write_elf_object`/`mold_find_crt_files`/`parse_linker_diagnostics` |
| A2 | **pass** (Fable) | `std.common.linker` contracts; specs 4/7/6 |
| A3 | **pass** after a Fable doc blocker | `link_engine_external_spec` 13/13 (2 red before); `SIMPLE_LINKER=internal` → UnsupportedFeature. Real link blocked by pre-existing bugs: SCV admission, and `doc/08_tracking/bug/native_linking_single_smf_temp_dir_result_not_unwrapped_2026-09-18.md`. Known limit: receipt engine id on cc fallback |
| A4a | **pass** after a Fable blocker | `reloc_engine_spec` 38/38 in both trees; oracle-based, rejects instead of masking; AArch64 ADRP (signed-21 range) / ADD / LDST64 (alignment). RISC-V pairing deferred. Wire-4 spec is a hand reproduction that A4b must replace |
| A5 | **pass** after 2 Fable blockers | 12 recipes; census fails closed; selftest cannot be bypassed; aarch64 LLVM census: 6 R_AARCH64 types; native-backend census blocked by SCV admission |

Next (post-RC1): A4b, A6, A12 can start. A7 waits on A6.

## 10. Post-RC1 lane status — 2026-09-19 (merged into `work/rc1-dataframe-sosix`)

| Lane | Result | Evidence |
|---|---|---|
| A4b loader convergence | **pass** after 2 Fable blockers (GOT lifetime; hot-reload GOT keying) | Both live loader loops use `smf_reloc_compute_wire`; out-of-range → `LoadResult.Error` (was a silent `as i32`). GotRel32 gets a per-module GOT tied to the exec mapping. `loader_reloc_oracle_spec` 9/9 (5 red before), `loader_reloc_wire4_spec` 5/5 driving the real `apply_smf_relocations`. `smf_dynlib` rejects wire 4 by name. The inline GOT in `module_loader_compat` is not reachable end to end here, because `native_make_executable` is refused before any relocation runs |
| A6 SMF link driver | **pass** (Fable) | `smf_link_driver` runs L2–L8 with 7 receipts; `impl ResolveProfile for SmfLinkProfile`; Local is module-private and Global beats Weak. Driver spec 8/8. Fixed 3 pre-existing gpu_smf reds (`resolve_core` `intern_name` hashed to 0 under the interpreter, bug filed) |
| A12 SMF read dedup | **pass** after a Fable fix | `smf_reader` is now a shim over `SmfReaderMemory` (−169 lines). Binding, type and section_index decode fixed (raw-u8 match defect). `open()` propagates symbol-table errors. Bug filed for the exported-set change |
| A7 ELF slice 1 | **pass** (Fable reproduced the runs) | `elf_static_link`: clang objects plus an archive fixpoint link into static ET_EXEC; they run on aarch64 (exit 42) and x86_64 under qemu (exit 42); segment and section parity with `ld.lld -static`. Not wired into `find_linker_path` |
| A4c reloc follow-up | **pass** (Fable) | Real JUMP26; LDST8/16/32/128; CALL26/JUMP26 range and alignment rejects; `reloc_engine_spec` 60/60 in both trees |

Next: A7 slice 2 (GOT/PLT/.dynamic/TLS for the LLVM/PIE corpus, and wiring `internal` behind `find_linker_path`), A9 boot layout, A11 conformance/perf.

## 11. Lane status — 2026-09-19 (second wave)

| Lane | Result | Evidence |
|---|---|---|
| A7 slice 2 | **pass** after a Fable blocker (GOTPCRELX relax on undefined-weak/ABS; shell chmod) | Static GOT, static PIE and dynamic libc exec/PIE on aarch64 all run (exit 42, "hi from libc"); x86_64 static under qemu. `readelf -l -S -d -r` parity with ld.lld. `SIMPLE_LINKER=internal` runs `internal:elf` through `link_request_to_native`; the default path is unchanged. x86_64 dynamic, TLS, COMMON and copy relocations are a named UnsupportedFeature. Gaps: no RELRO, `.gnu.hash`, symbol versions or `.symtab`. Bug filed: `nogc_sync_mut file_set_mode` is a no-op stub |
| A9 boot layout | **rung 2** (Fable pass) | All 50 in-tree `.ld` parse and round-trip; BootLayoutPlan built for all 6 SimpleOS arch scripts. Rung 3 needs `elf_exec_writer` VMA/LMA/PHDRS support (next). Board blocked (record filed). The real-firmware gate baseline boots hello via EDK2 → Limine |
| A11 conformance | **pass** (Fable) | `check-link-mutation-gates.shs`: 7/7 mutations turn their spec red on the merged tree; selftest runs in CI. Timing on the fixtures: internal ~0.37 s / 150 MB (seed interpreter) vs ld.lld/mold <10 ms / ~20 MB |

Next: A9 rung 3 (BootLayoutPlan in the ELF writer + `ld.lld -T` parity), `link_to_native` routing for `internal` (native_linking owner), RELRO and `.gnu.hash`, x86_64 PLT, and running the engine natively instead of in the interpreter for speed.

## 12. Lane status — 2026-09-19 (third wave: B1/B2/B3)

| Lane | Result | Evidence |
|---|---|---|
| B1 A9 rung 3 (`elf_boot_link`) | **pass** after 2 Fable blockers | Round 1 fixed: ASSERT used the wrong operator precedence (`1<2 && 5<3` was true); `AT>` was ignored; there were no VMA/LMA/PT_LOAD overlap or MEMORY-overflow rejects. Round 2 fixed: a region used as both `>` and `AT>` advanced twice; a NOBITS `AT>` did not advance its region; an explicit address was moved by `ALIGN()`; MIN/MAX and `/` `%` were signed. Each fix has a red→green spec, matched against ld.lld 23: `elf_boot_link` 25/25, `boot_layout_ops` 17/17 (both trees). The hello kernel's loaded bytes are identical to `ld.lld -O0 --no-relax`. **Rung 4 PARTIAL:** EDK2→Limine boots both kernels, and their serial logs are byte-identical. The gate still FAILs for both, because it needs full-kernel `[BOOT]` markers. The sha256 evidence is local-only (`build/os/b1/`). The board is blocked (record updated) |
| B2 ELF extras | **pass** (Fable) | `.gnu.hash` is byte-identical to the ld.lld oracle; `.symtab`/`.strtab` are emitted; x86_64 dynamic PLT/GOT is structural and gated as UnsupportedFeature (no execution proof). `elf_gnu_hash` 6/6, `elf_symtab` 6/6, `elf_x64_dynamic` 7/7 |
| B3 `link_to_native` routing | **pass** after a Fable blocker (config fields silently dropped) | `SIMPLE_LINKER=internal` routes `link_to_native` to `internal:elf` through a helper shared with `link_request_to_native`. Unsupported `NativeLinkConfig` fields are rejected by name. The single-SMF `create_temp_dir` Result bug is fixed. `native_linking_internal_spec` 5/5; the default path is unchanged |

Merged tree: 27/27 linker specs green; `check-link-mutation-gates.shs` PASS (7/7).

Next: RELRO, section GC, lld `-O1` string merge, a full-kernel rung 4 (the real gate markers), the x86_64 dynamic execution proof, and native (non-interpreted) engine speed.

## 13. Lane status — 2026-09-19 (F1: linking the `simple` binary itself)

**Which linker links the `simple` binary today.** The question had two
candidate routes and the answer is the Simple one, which is the opposite of
what the seed's presence suggests:

* The sanctioned bootstrap links stage2 and stage3 `simple` with
  `native-build --target <triple> --backend llvm --runtime-bundle
  core-c-bootstrap --source src/compiler --source src/app --source src/lib
  --entry-closure --runtime-path <stage2-runtime-authority> --entry
  src/app/cli/bootstrap_main.spl -o <stage bin>`
  (`scripts/bootstrap/bootstrap-from-scratch.sh:2959` and `:3036`). Observed
  live on this host on 2026-09-19 as a real stage-3 process from a parallel
  bootstrap lane, so this is not a reading of the script alone.
* `native-build` is **Simple**, interpreted by the seed:
  `src/app/cli/native_build_main.spl` → `native_build_worker.spl` →
  `cli_native_build_with_environment_variant_policy_v1` ->
  `driver_aot_native_output.spl:2235` `link_llvm_native(object_files, output,
  llvm_opts)` -> `llvm_native_link.spl` -> `llvm_native_link_orchestrator.spl:648`
  `link_to_native(all_objects, output, link_config)` (every arrow grepped, not
  inferred). That is the Simple-side
  wrapper, so lane B3's `SIMPLE_LINKER=internal` route **is** on the path that
  links the compiler itself.
* The Rust seed's own `native_project/linker.rs` is therefore **not** the route
  for the stage binaries. It is still the route for the Rust artifacts the
  bootstrap consumes (`cargo build -p simple-driver / simple-native-all /
  simple-runtime / simple-compiler-backfill`, linked by rustc's own `cc`), and
  it rejects `internal` outright: `linker_alias` (`linker.rs:43-56`) accepts
  only `mold`/`lld`/`ld.lld`/`lld-link`/`ld`/`gnu`/`bfd` and answers
  `Unsupported SIMPLE_LINKER value: internal`. That reject is correct — there
  is no internal engine on the Rust side — and it means `SIMPLE_LINKER=internal`
  can never apply to the Rust half of the bootstrap.

| Lane | Result | Evidence |
|---|---|---|
| F1 library search | **pass** | `NativeLinkConfig.libraries`/`library_paths` were lane B3 rejects and are now honoured: ld's order (caller `-L` entries, then the host crt libdir; `lib<name>.so` before `lib<name>.a`), a `lib<name>.so` that is a GNU ld script followed to its `GROUP()` members (required on glibc — `/usr/lib/aarch64-linux-gnu/libm.so` is a script, not ELF), inputs classified by ar/ELF magic rather than extension. `libraries=["m"]` links `hello_libm_a64.o` and the binary prints `sqrt=42`, exit 42 |
| F1 DT_NEEDED parity | **pass, and it caught a real defect** | The first `GROUP()` parser also returned the `AS_NEEDED()` member, because the keyword and its `(` are separated by whitespace in glibc's script. Result was an extra `DT_NEEDED libmvec.so.1` that `ld.lld` does not emit — found by diffing `readelf -dW` against an external link, not by reading the code. Fixed and pinned by a parity spec |
| F1 `runtime_path: "none"` | **pass** | The bootstrap stage link's own `NativeLinkConfig` carries `runtime_path: "none"`, the documented sentinel for "the LLVM pipeline supplies the runtime objects directly". Rejecting it was a false reject with nothing to honour, and it stopped the internal route at the one call site that links the compiler. A real `runtime_path` still rejects by name |
| F1 full self-host link | **NOT achieved — blocked, stated as such** | See the ranked gap list below. No partial result is reported as a success |

`native_linking_internal_spec` 5/13 → 13/13 (both trees byte-identical). All 27
linker specs re-run individually: 27/27 `outcome=OK`, 0 failed.

### Ranked gaps for a full self-host internal link

1. **`retained_symbols` has no engine input.** It is the remaining hard reject
   on the real bootstrap link config (`llvm_external_provider_retained_symbols`
   fills it). `ElfLinkRequest` carries only `entry` — there is no extra-GC-roots
   field — so a retained symbol living in an otherwise-unneeded archive member
   would be dropped by the fixpoint. Needs an `elf_static_link.spl` change
   (lane A7's file), not a `native_linking.spl` one.
2. **TLS.** The deployed `simple` has `FLAGS BIND_NOW STATIC_TLS`; TLS
   relocations are a named `UnsupportedFeature` in the engine (plan §11).
3. **Interpreted-engine cost at real scale.** Measured on this host: the
   per-byte `[i64]` widening `internal_link_native_read_i64` performs runs
   100 MB in 9.2 s at 1.28 GB RSS under the JIT. The stage-3 link's inputs are
   411 MB of archives (`libsimple_native_all.a` 390 MB,
   `libsimple_compiler_backfill.a` 21 MB, `deps/libsimple_runtime.a` 43 MB),
   so widening alone projects to ~40 s and >5 GB before any resolution,
   fixpoint or relocation work — and the engine body runs interpreted, not
   JIT-compiled. Plan §11 already names "running the engine natively instead
   of in the interpreter" as required work; this is the measurement for it.
4. **RELRO, symbol versions, section GC, `-O1` string merge** — already named
   in §11/§12 as next work; the compiler's own link needs at least RELRO
   (`BIND_NOW` is set on the shipped binary).
5. **The stage-link inputs are not fully retained on this host.** The stage-3
   directory keeps the three archives but not the generated entry object, and
   no archive defines `main` (`nm --defined-only` over all three finds none),
   so the real stage link cannot be reconstructed from retained artifacts — it
   has to be re-driven through `native-build`.

### Internal vs external, same object, measured 2026-09-19 (aarch64 host)

`hello_libm_a64.o` + `libraries=["m"]`, internal (`SIMPLE_LINKER=internal`,
through `link_to_native`) against `ld.lld 23` with the equivalent argv.

| | internal | ld.lld |
|---|---|---|
| runs | `sqrt=42`, exit 42 | `sqrt=42`, exit 42 |
| size | 4,392 B | 5,352 B |
| `DT_NEEDED` | `libc.so.6`, `libm.so.6` | `libc.so.6`, `libm.so.6` (identical **after** the AS_NEEDED fix; before it the internal output carried a third, `libmvec.so.1`) |
| segments | `PHDR INTERP NOTE LOAD×3 DYNAMIC GNU_STACK` | same plus `GNU_RELRO`, `LOAD×4` |
| sections only in ld.lld's output | — | `.gnu.version`, `.gnu.version_r`, `.relro_padding`, `.comment` |

The deltas are exactly the already-named gaps: no RELRO (hence 3 `PT_LOAD`
instead of 4 and no `.relro_padding`) and no symbol versions. Nothing here is
a silent difference — `.gnu.hash`, `.symtab`/`.strtab`, `.rela.dyn`,
`.rela.plt`, `.plt`, `.got`/`.got.plt` are all present and the DT_NEEDED set
matches byte for byte.

### What was NOT done, stated plainly

No internally linked `simple` binary exists, so `<out> --version`, a hello-world
compile with it, and a spec run on it **did not happen**. The end-to-end
`native-build` run that would have produced one is blocked on this host before
the link step by SCV source-inventory admission, not by the linker:

```
$ SIMPLE_SCV_INVENTORY_COLD_INIT=1 SIMPLE_BOOTSTRAP=1 SIMPLE_LINKER=internal \
    bin/simple native-build hello.spl -o hello_internal
SCV-E-ADMISSION: filesystem-event-journal-missing        # cursor claims filesystem_rows=1 with the empty-string digest and no .scv/journal/events.log
wall=247.31s rss=26942684kB rc=1
# after rm -rf build/scv .simple:
SCV-E-SNAPSHOT: snapshot-inventory-unavailable
wall=157.82s rss=28078696kB rc=1
```

Two things worth recording independently of the linker: the SCV cursor
`build/scv/compile-events/CURRENT` published `filesystem_rows=1` with
`filesystem_digest` = the sha256 of the empty string and no journal file, which
is a state the guard correctly refuses and nothing here can repair; and the
interpreted native-build worker peaked at **27 GB RSS for a two-line hello
world**, which is the same class of problem as gap 3 above.

A full self-host internal link does **not** need a deployed pure-Simple binary
— the seed interprets `native-build`, and that is the path to `link_to_native`.
The wall is the interpreted engine's cost at 411 MB of archive input, plus
`retained_symbols` and TLS.
