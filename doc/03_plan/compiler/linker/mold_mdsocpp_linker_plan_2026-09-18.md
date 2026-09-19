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
| C3 A9 rung 4, full kernel | **pass** | The gate PASSES with the REAL SimpleOS aarch64 Limine kernel linked by `elf_boot_link` (`PASS — 4 boot-stage marker(s) checked ... 91 serial line(s)`, exit 0, EDK2/AAVMF pflash -> BOOTAA64.EFI, no `-kernel`). Loaded bytes byte-identical to `ld.lld -O0 --no-relax` over both LOAD segments; `llvm-nm -g --defined-only` gives 626 symbols on each side with identical names and values (only `_bss_end`/`_kernel_end` differ in nm type letter). sha256: internal `ea0de1d1…`, ld.lld `73283884…`. Four upstream defects had to be fixed first — the kernel did not link with ld.lld either: `mmio_disable_test_mode` dropped by merge `e274cd33719`, 19 unimplemented `rt_arm64_*` accessors, missing `rt_value_u64`/`rt_value_as_u64`/`rt_unwrap_or_trap`, and `__simple_call_module_inits` never called on a freestanding link (NULL module globals -> Data Abort in `pmm`). Details: `doc/08_tracking/bug/boot_layout_a9_board_blocked_2026-09-19.md` |

Merged tree: 27/27 linker specs green; `check-link-mutation-gates.shs` PASS (7/7).

Next: RELRO, section GC, lld `-O1` string merge, a full-kernel rung 4 (the real gate markers), the x86_64 dynamic execution proof, and native (non-interpreted) engine speed.

## 13. Lane status — 2026-09-19 (fourth wave: C1)

| Lane | Result | Evidence |
|---|---|---|
| C1 RELRO / section GC / string merge | **pass** (3 commits on `work/lnk-c1`) | **RELRO:** `elf_exec_plan` splits the RW class at a `.relro_padding` NOBITS marker — RELRO load padded to the 4 KiB common page, the rest at the next 64 KiB max-page, `PT_GNU_RELRO` (R, align 1) after `PT_DYNAMIC`. RW section order, page ends and segment shape match `ld.lld-23 -z relro` on the new `relro_a64.o`; dynamic PIE/exec, static PIE and static-with-`.got` all still run (exit 42). Absolute sizes differ from lld only through two PRE-EXISTING gaps (no symbol versioning: 3 fewer `.dynamic` tags; no `__gmon_start__` export: one fewer PLT slot), so the spec derives them from our own headers. `elf_relro_spec` 9/9 (8 red before). **GC:** new `elf/gc_sections.spl`, opt-in via `ElfLinkRequest.gc_sections`; roots are ld.lld `isReserved` + entry. Kept sizes byte-identical to `ld.lld --gc-sections` on `gc_a64.o` (`.rodata` 0x4 / `.text` 0x80 / `.init` 8 / `.init_array` 8 / `.data` 8 / `.bss` 0x10), lld's `--print-gc-sections` list matches the symbols that leave our `.symtab`. `.eh_frame` per-FDE liveness, `SHT_GROUP` and `SHF_LINK_ORDER` are named errors. `elf_gc_sections_spec` 8/8 (5 red before). **Merge:** new `elf/merge_sections.spl`, on by default like lld `-O1`; same group key and placement as lld's `MergeSyntheticSection`, addend folded through the piece map. Merged `.rodata` is 0x19 bytes with the same four literals as `ld.lld -O1` (0x22 with `-O0`), and the executed exit status discriminates: 42 merged / 40 not. `elf_merge_strings_spec` 7/7, mutation-proved. |

Known gap (filed, not masked): the merged blob's BYTE ORDER is
first-appearance, while ld.lld orders pieces by the top bits of an XXH3-64
hash across 32 shards —
`doc/08_tracking/bug/elf_merge_string_order_not_lld_shard_order_2026-09-19.md`.

19 linker specs green on this lane. Next: x86_64 execution proof (lane C2),
symbol versioning, `-z now`/`DF_BIND_NOW`, ICF, and the XXH3 shard order above.
## 14. Lane C2 — x86_64 dynamic execution proof (2026-09-19)

| Lane | Result | Evidence |
|---|---|---|
| C2 x86_64 dynamic glibc | **run passes; gate lifted** | Sysroot: Ubuntu noble amd64 `libc6`/`libc6-dev` 2.39-0ubuntu8.9 (+ libgcc-s1, linux-libc-dev, libcrypt-dev), fetched without root through a private apt state dir and `dpkg-deb -x` into `$HOME/.cache/x64-sysroot/root` (recipe and sha256s in `test/fixtures/linker/elf/RECIPE.md`). `elf_link` links `crt1.o`/`Scrt1.o` + `crti.o` + `hello_libc_x64.o` + `crtn.o` + `libc.so.6` into a dynamic ET_EXEC and a PIE. Both print `hi from libc` and exit 42 under `qemu-x86_64 -L <sysroot>`. The one engine defect was that `_GLOBAL_OFFSET_TABLE_` (an UND symbol in x86_64 `crt1.o`/`crti.o` with no relocation) was undefined; it is now linker-defined at `.got.plt` on x86_64 and `.got` on aarch64, as in ld.lld. The UnsupportedFeature gate and `elf_link_structural` are removed. `elf_x64_dynamic_exec_spec` 4/4 (red 2/4 before); without a sysroot or qemu it prints `SKIP: x64-sysroot-missing` / `SKIP: qemu-x86_64-missing` and asserts that reason. `elf_x64_dynamic_spec` 7/7 |

Differences from `ld.lld-23` with the same inputs (`readelf -lSdrW`). None of them stops the run: the PLT/GOT shape, JUMP_SLOT/GLOB_DAT for `puts`/`exit`/`__libc_start_main`, and the `lea main(%rip)` relaxation match. The engine output has no `.gnu.version`/`.gnu.version_r` (no symbol versioning), no RELRO or `.relro_padding`, and no `.comment`, and leaves EI_OSABI at 0 where ld.lld sets 3/GNU. Undefined-weak `__gmon_start__` becomes a constant-0 GOT slot, where ld.lld uses a GLOB_DAT. The three input `.note.gnu.property` notes (IBT/SHSTK from crt objects) are concatenated rather than merged. ld.lld drops them because `hello_libc_x64.o` has none. No `PT_GNU_PROPERTY` is emitted, so the loader ignores them, but the section is wrong: open, `doc/08_tracking/bug/internal_elf_linker_gnu_property_notes_concatenated_2026-09-19.md`.

### C2 round 2 — Fable BLOCK: the gate lift needed these three first (2026-09-19)

The hello fixture avoided every symbol that carries a glibc compat version, so
the execution proof was real but narrow. Each item below was a silently wrong
binary with no error, and each now has a red→green spec and a mutation row in
`check-link-mutation-gates.shs` (7 rows -> 11).

| item | before | now |
|---|---|---|
| Symbol versioning | `shared_object` read versym only to drop hidden exports; no `.gnu.version_r`. ld.so resolves a versionless reference to the library's version index 2 = **GLIBC_2.2.5 on x86_64**, i.e. the whole compat set (memcpy, pthread_cond_*, posix_spawn…) binds to the OLD implementation. `realpath("/", NULL)` returned NULL, rc=7. aarch64 never showed it: its index 2 is GLIBC_2.17 | `.gnu.version_d` is parsed (BASE verdef excluded), each import's default version recorded, and `.gnu.version` + `.gnu.version_r` + DT_VERSYM/VERNEED/VERNEEDNUM emitted. Indices match ld.lld's on the same inputs (2=GLIBC_2.34, 3=GLIBC_2.3, 4=GLIBC_2.2.5). `realpath=/`, rc=42, exec and PIE |
| Locally defined IFUNC | only imported type-10 was handled; a defined IFUNC fell through as a plain FUNC and its address was the resolver's (rc=192 vs ld.lld's 42). Pre-existing and arch-neutral, made reachable by the gate lift | rejected by name: `UnsupportedFeature: locally defined STT_GNU_IFUNC needs an R_*_IRELATIVE relocation …: f` |
| Vacuous spec verdict | `expect_named_skip` printed the reason to stdout and reported `passed=4 skipped=0 PASS` with no sysroot — test_db recorded a proof that never ran | `skip_if` from `std.spec.decorators`: the verdict's `executed=` drops from 7 to 1 and each line reads `skipped (x86_64 run environment missing: …)`. Two residual runner defects filed: decorator-invoked examples print `unnamed`, and the VERDICT's `skipped=` field stays 0 (`doc/08_tracking/bug/spec_decorator_examples_unnamed_and_uncounted_2026-09-19.md`) |

Also in this round:

- `reloc_scan` gained `RC_TLS`. x86_64 GOTTPOFF (22) used to fall through to the
  shared-library `else` and be reported as "needs a copy relocation or canonical
  PLT; recompile with -fPIC". TLS relocations on both targets are now named as
  TLS.
- The `.note.gnu.property` mitigation moved into this lane: the notes are
  dropped when the `FEATURE_1_AND` across all inputs is 0 (ld.lld's own result)
  and the link is refused by name when it is not, since no `PT_GNU_PROPERTY` is
  emitted. Real merging stays open in the bug record.
- **Weak-undef policy, documented at the decision site** (`elf_symref`): an
  undefined weak symbol is NEVER made dynamic here — it resolves statically to
  0. ld.lld instead emits a `.dynsym` entry with `R_*_GLOB_DAT`, which is why
  `__gmon_start__` is in its output and not in ours. Ours is safe *only*
  because crt1/crti guard the call on the slot being non-zero. Any weak symbol
  a later-loaded object is expected to supply would silently stay 0.
- `_GLOBAL_OFFSET_TABLE_` follows ld.lld's per-target base (`.got.plt` on
  x86_64, `.got` on aarch64).

All 26 `test/01_unit/.../linker` specs green.

#### C2 round 3 — Fable PASS with five accuracy items (2026-09-19)

Fable verified versioning end to end against ld.lld-23 (two verneed chains in
both link orders, a symbol with different default versions in two libraries,
`@@` plus `@`, weak-undef, `.gnu.version` count == dynsym count on 15 binaries,
aarch64 exec + PIE still at 42). Fixed here:

1. **An unversioned import is now `VER_NDX_GLOBAL` (1)**, not 0. Measured
   ld.lld on a mixed link (`add_val` from an unversioned DSO plus versioned
   glibc): it writes `1 (*global*)`. 0 is `VER_NDX_LOCAL` and is for symbols
   that are not imports. glibc treats them alike; the gABI does not, so we
   match ld.lld.
2. **The index-numbering claim is corrected to "self-consistent", not
   "matches ld.lld"** — on aarch64 ours are 2=GLIBC_2.34, 3=GLIBC_2.17 where
   ld.lld's are reversed. The spec pins OUR first-use numbering and adds the
   real property: every `.gnu.version` entry names an index the verneed
   defines.
3. **`vna_flags` carries `VER_FLG_WEAK`**: `shared_object` now reads each
   verdef's flags and `elf_ver_plan` propagates them. No glibc version is weak,
   so nothing changes for the corpus — it is asserted as 0 rather than assumed.
4. **The vestigial `drop_property` parameter is gone.** `elf_property_policy`
   returns `Result<(), text>` (admit or refuse by name) and `elf_static_place`
   never places a property note, since the only links that reach it are the
   ones whose notes must be dropped.
5. **The sysroot-dependent mutation rows fail closed.** Without an x86_64
   sysroot their specs skip, so the mutation would read VACUOUS —
   indistinguishable from a gate that has stopped protecting.
   `check-link-mutation-gates.shs` now ERRORs by name instead.

Also: `.symver name, name@VERSION` used to be refused as `undefined symbol:
realpath@GLIBC_2.2.5`, which is a true refusal with a false reason — the symbol
exists under that version. It now names the unsupported explicit-symver form
and says that references bind to each library's default version. Fixture
`symver_x64.o`, spec `elf_link - explicit symbol versions`.

## 15. C1 + C2 merged (2026-09-19)

`work/lnk-c1` and `work/lnk-c2` are independent and land as a union, not a
choice. §13's "no symbol versioning" and §14's "no RELRO or `.relro_padding`,
no `.gnu.version`/`.gnu.version_r`" are both statements about the UNMERGED
lanes: the merged linker emits RELRO, supports `--gc-sections` and SHF_MERGE
string merging, AND emits `.gnu.version`/`.gnu.version_r` + DT_VERSYM/VERNEED/
VERNEEDNUM. The one shared call site, `elf_static_place`, takes C1's
`(objects, live, merged)` and additionally skips `.note.gnu.property` inputs;
`elf_property_policy` is evaluated before the gc/merge passes so its reject
keeps C2's ordering. What remains unsupported after the merge: COMDAT dedup,
locally defined IFUNC (no IRELATIVE), property-note merging, explicit
`.symver`, TLS, COMMON, copy relocations / canonical PLTs and text relocs.
## 16. Lane status — 2026-09-19 (F1: linking the `simple` binary itself)

**Which linker links the `simple` binary today.** The question had two
candidate routes and the answer is the Simple one, which is the opposite of
**CORRECTED 2026-09-19 (round 2, Fable block).** The first version of this
section said both stage binaries link through the Simple-side wrapper. That is
wrong for stage 2, and the two stages do not even share a chain.

* **Stage 2 links through the RUST path.**
  `scripts/bootstrap/bootstrap-from-scratch.sh:2945` sets
  `SIMPLE_NATIVE_BUILD_RUST=1` (and `:2958` `SIMPLE_BINARY=<seed>`) for the
  `:2959` `native-build`, which `driver/src/main.rs:168-178` routes to the Rust
  handler -> `native_build.rs:662` -> `native_project/mod.rs:1216 link_objects`
  -> `linker.rs:1165` -> `:54`, where `linker_alias` answers
  `Unsupported SIMPLE_LINKER value: internal`. So the Rust linker links the
  stage-2 OBJECTS, not merely the cargo artifacts, and **a real
  `SIMPLE_LINKER=internal` bootstrap dies at stage 2 before stage 3 is ever
  reached.** Closing this needs either the Rust path taught to delegate to the
  internal engine, or the bootstrap taught to use the Simple path for stage 2.
* **Stage 3 is Simple-side**, and `:3036` does NOT set
  `SIMPLE_NATIVE_BUILD_RUST`. It is driven by the stage-2 binary, i.e. the
  bootstrap CLI: `src/app/cli/bootstrap_main.spl:385` ->
  `run_exact_stage3_focused_capsule` / `bootstrap_focused_native_build` ->
  `compiler.driver.bootstrap_api_fixed.aot_native_project_with_backend_fixed`
  -> `driver_aot_native_output` -> `llvm_native_link_orchestrator.spl:648`
  `link_to_native(all_objects, output, link_config)`. **Not**
  `native_build_main.spl` / `native_build_worker.spl`, which is what the first
  version of this section claimed. Even here the internal route is refused, by
  `retained_symbols` in the config built at `orchestrator:633-640`.
* The Rust seed's `linker.rs` is therefore the route for the cargo artifacts
  **and for stage 2**. Its reject is correct — there is no internal engine on
  the Rust side — but it is a hard stop for this lane's goal, not a detail.

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
| F1 library search | **pass** | `NativeLinkConfig.libraries`/`library_paths` were lane B3 rejects and are now honoured: caller `-L` entries in order, then the host crt libdir, `lib<name>.so` before `lib<name>.a`. That trailing crt libdir is an IMPLICIT DEFAULT that ld.lld does not have -- measured, `ld.lld-23 ... -lc` with no `-L` fails `unable to find library -lc` while this engine links -- so on that one point the engine follows ld.bfd, not lld. Deliberate and kept; named here because "ld's order" overclaimed it, a `lib<name>.so` that is a GNU ld script followed to its `GROUP()` members (required on glibc — `/usr/lib/aarch64-linux-gnu/libm.so` is a script, not ELF), inputs classified by ar/ELF magic rather than extension. `libraries=["m"]` links `hello_libm_a64.o` and the binary prints `sqrt=42`, exit 42 |
| F1 DT_NEEDED parity | **pass, and it caught a real defect** | The first `GROUP()` parser also returned the `AS_NEEDED()` member, because the keyword and its `(` are separated by whitespace in glibc's script. Result was an extra `DT_NEEDED libmvec.so.1` that `ld.lld` does not emit — found by diffing `readelf -dW` against an external link, not by reading the code. Fixed and pinned by a parity spec |
| F1 `runtime_path: "none"` | **pass** | The bootstrap stage link's own `NativeLinkConfig` carries `runtime_path: "none"`, the documented sentinel for "the LLVM pipeline supplies the runtime objects directly". Rejecting it was a false reject with nothing to honour, and it stopped the internal route at the one call site that links the compiler. A real `runtime_path` still rejects by name |
| F1 full self-host link | **NOT achieved — blocked, stated as such** | See the ranked gap list below. No partial result is reported as a success |

`native_linking_internal_spec` 5/14 → 14/14 (both trees byte-identical; the
last two examples were added later in the lane, hence the 13/13 and 14/14
figures below — the numbers are chronological). All 27
linker specs re-run individually at `9782b90b0b3`: 27/27 `outcome=OK`, 0
failed. The only two that import the changed file
(`native_linking_internal_spec`, `link_engine_external_spec`) were re-run at
the lane tip; the other 25 do not import it.

### Ranked gaps for a full self-host internal link

1. **`retained_symbols` has no engine input.** It is the remaining hard reject
   on the real bootstrap link config (`llvm_external_provider_retained_symbols`
   fills it). `ElfLinkRequest` carries only `entry` — there is no extra-GC-roots
   field — so a retained symbol living in an otherwise-unneeded archive member
   would be dropped by the fixpoint. Needs an `elf_static_link.spl` change
   (lane A7's file), not a `native_linking.spl` one.
2. **No `--allow-multiple-definition` mode.** The real stage config sets
   `allow_duplicate_definitions: not stage4_requested` = `true`, and the
   external path honours it by passing `--allow-multiple-definition`
   (`native_linking.spl:140,145,1462`). The compiler corpus genuinely carries
   duplicates — one native-build run on this host warned about `shell` x4,
   `process_wait` x3, `process_run_with_limits` x3, `env_vars` x2,
   `file_read_text_at` x2, `rotr32` x2, `sha256_process_block` x2. The
   internal engine has no such mode and treats a duplicate strong definition
   as a loud error, which is exactly why lane B3 left this field off the
   reject list — so the real link fails on the first duplicate. Loud is
   correct; it is still a blocker, and it is not currently rejected by name.
3. **TLS.** The deployed `simple` has `FLAGS BIND_NOW STATIC_TLS`; TLS
   relocations are a named `UnsupportedFeature` in the engine (plan §11).
4. **Interpreted-engine cost at real scale.** Measured on this host: the
   per-byte `[i64]` widening `internal_link_native_read_i64` performs runs
   100 MB in 9.2 s at 1.28 GB RSS under the JIT. The stage-3 link's inputs are
   411 MB of archives (`libsimple_native_all.a` 390 MB,
   `libsimple_compiler_backfill.a` 21 MB, `deps/libsimple_runtime.a` 43 MB),
   so widening alone projects to ~40 s and >5 GB before any resolution,
   fixpoint or relocation work — and the engine body runs interpreted, not
   JIT-compiled. Plan §11 already names "running the engine natively instead
   of in the interpreter" as required work; this is the measurement for it.
5. **RELRO, symbol versions, section GC, `-O1` string merge** — already named
   in §11/§12 as next work; the compiler's own link needs at least RELRO
   (`BIND_NOW` is set on the shipped binary).
6. **The stage-link inputs are not fully retained on this host.** The stage-3
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

**CORRECTED (round 2).** The row above compared the DT_NEEDED SET and the
sentence that stood here -- "the DT_NEEDED set matches byte for byte ... nothing
here is a silent difference" -- was false, because it never compared ORDER.
Order is load-bearing: the loader resolves a symbol from the FIRST DT_NEEDED
entry that defines it. This engine seeded its shared-input list with libc
FIRST, where ld.lld emits the `-l` libraries first and libc last. On this very
fixture, MEASURED: ld.lld emits `libm.so.6 libc.so.6`; ours emitted
`libc.so.6 libm.so.6` before the fix and `libm.so.6 libc.so.6` after it. (An
earlier draft of this line claimed lld emitted `libm libmvec libc` -- that was
not measured and is wrong: libmvec is AS_NEEDED and unused here, so lld emits
no entry for it. The `libmvec` in the round-1 record belongs to OUR pre-fix
output, not to lld's.)
Measured consequence, not a theoretical one: an object calling `atoi` linked
with a library whose `atoi` returns 42 exits **1** under the old order (libc
wins) and **42** under ld.lld. Fixed, and pinned by a spec that asserts the
ORDER and the exit status. The remaining structural deltas are the
already-named gaps: no RELRO (hence 3 `PT_LOAD` instead of 4 and no
`.relro_padding`) and no symbol versions.

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
# third attempt, adding the documented remedy SIMPLE_SCV_FREEZE_FALLBACK=1:
SCV-E-ADMISSION: filesystem-event-journal-missing
wall=356.55s rss=26520188kB rc=1        # no output file produced
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

### Second parity defect, also found by comparison rather than by reading

`libraries=["c"]` emitted **two** `DT_NEEDED libc.so.6` entries. The implicit
libc input is `{libdir}/libc.so.6` while `libc.so`'s `GROUP()` names
`/lib/<triple>/libc.so.6` — textually different, the same file — and this
engine writes one `DT_NEEDED` per shared input, whereas `ld.lld` keys on
SONAME and emits one. Shared inputs are now de-duplicated by content digest.
Red → green: `native_linking_internal_spec` 13/14 → 14/14, both trees
identical. The real bootstrap link config passes `libraries: []`, so this was
not on the critical path — it was on the path of anything that starts passing
`-l` names, which is where this lane is heading.

Three attempts, three refusals, 158-357 s and 26-28 GB RSS each, none of them
reaching the link step. The cursor is republished with `filesystem_rows=1` and
no journal on every run, so wiping `build/scv` does not clear it. The guard is
right to refuse and there is a way to make it pass — write an empty
`.scv/journal/events.log`, whose sha256 is exactly the `filesystem_digest` the
cursor already carries — but that is fabricating the state a fail-closed guard
exists to check, so it was not done. **`SIMPLE_LINKER=internal` has therefore
never been exercised end to end through `native-build` on this host; every
internal-engine result in this lane comes from `link_to_native` driven
directly by a spec.** Filing the SCV cursor defect belongs to whoever owns
`src/app/compiler_entrypoint/inventory_events.spl`.

### Round 2 (Fable block): what was fixed, what is still a gap

Fixed, each with a red→green spec in `native_linking_internal_spec` (20
examples, both trees byte-identical):

| | before | after |
|---|---|---|
| DT_NEEDED order | libc first; a shadowing `-l` library lost, exit **1** | `-l` libraries first, libc last, exit **42** — same order as ld.lld. Dedup keeps the FIRST occurrence, as ld does by SONAME, so an explicit `-lc` keeps its own position |
| `-l:<file>` literal form | searched for `lib:libfoo.a.so`, unresolvable | resolves that exact file name; the error names the literal form |
| relative ld-script members | `libgcc_s.so` = `GROUP ( libgcc_s.so.1 -lgcc )` reported "neither ELF nor a GNU ld script" | relative members resolve against the script's own directory then the search path; `-lNAME` members re-enter the search (depth-bounded, cycles named) |
| `OUTPUT_FORMAT` argument | would have been collected as a member once non-absolute tokens were accepted | members are collected only inside `GROUP()`/`INPUT()` |
| all-AS_NEEDED script | "neither ELF nor a GNU ld script" — the wrong cause | names AS_NEEDED, lists the members, and says it is a capability gap |

Still gaps, both located in `elf_static_link.spl` / `ElfLinkRequest` (lane A7's
file), not in `native_linking.spl`, and both measured against ld.lld:

1. **`.so` with no usable DT_SONAME.** Two sub-cases; this entry previously
   collapsed them into one.
   * **No DT_SONAME at all** — MEASURED: ld.lld records the FILE NAME
     (`DT_NEEDED libemptyson_f1.so`); this engine answers `internal engine:
     shared object 0: shared object has no DT_SONAME (needed for DT_NEEDED)`.
     `ElfLinkRequest.shared` carries bytes only — no file name — so the
     fallback cannot be supplied from the wrapper (lane A7's file).
   * **DT_SONAME present but the empty string** — reported to make ld.lld emit
     `DT_NEEDED ""` and de-duplicate two such libraries ON that empty string.
     NOT verified here: GNU ld refuses to write one ("SONAME must not be empty
     string; ignored"), so producing the input needs a hand-built ELF. If that
     is right, our content-digest fallback diverges for this sub-case too — it
     keys such libraries apart where lld merges them. Recorded, not claimed
     fixed.
2. **AS_NEEDED member whose symbol IS used.** ld.lld keeps the library
   (measured: `DT_NEEDED libneeded_f1.so`); this engine cannot, because it
   emits one DT_NEEDED per shared input unconditionally. Real as-needed needs
   a per-library flag on `ElfLinkRequest.shared` so DT_NEEDED is written only
   when the resolver actually took a symbol from that library. The error now
   names this instead of misreporting the script as malformed.

All 27 linker specs re-run individually at `f38a070708b` (the round-2 fix):
27/27 `outcome=OK`, 0 failed — not just the two importers, because the round-2
change altered shared-input ordering, which any spec that links could see.

### Round 3 (Fable block): dedup keys on SONAME, not bytes

The round-2 dedup keyed on `file_hash_sha256` while its own comment claimed
"as ld does by SONAME" — the code and the claim disagreed, the same defect
class as round 2's "matches byte for byte". Two DIFFERENT files can carry the
SAME SONAME (a script member given by an absolute path plus a `-l` to a local
build of the same library — glibc's `libc.so` names `/lib/<triple>/libc.so.6`
absolutely, so this is the ordinary shape, not a contrived one). Measured with
`soname_alias/libother_a64.so` (different bytes, SONAME `libshadowatoi_a64.so`):

| | before | after / ld.lld |
|---|---|---|
| `libraries=["shadowatoi_a64","other_a64"]`, two `-L` dirs | `libshadowatoi_a64.so libshadowatoi_a64.so libc.so.6` | `libshadowatoi_a64.so libc.so.6` |

`internal_shared_dedup_key` now reads DT_SONAME via `elf_parse_shared` and
falls back to the content digest only for a library with no SONAME. That
fallback never decides a real link — a no-SONAME library is refused further
down — it only keeps the function total so two such inputs cannot collide on
the empty string.

**It does not make the no-SONAME gap cheap to close, so that gap stays
recorded.** `elf_static_link` needs a name to write into DT_NEEDED and
`ElfLinkRequest.shared` carries bytes only; supplying ld's fallback (the file
name) still needs a field on that struct, which is lane A7's file. Keying the
*dedup* on SONAME is independent of that.

`native_linking_internal_spec` 20/21 → 21/21, both trees byte-identical.

All 27 linker specs re-run individually at `cc758db2ea5` (the round-3 SONAME
dedup): 27/27 `outcome=OK`, 0 failed. The only later commit, `d2a5ba6fc98`, is
comment-only.

Verified under real concurrency rather than by inspection: both trees' copies
of `native_linking_internal_spec` run at the same time now give
`outcome=OK ... passed=21 failed=0` and rc 0, where the fixed `/tmp` names had
each run linking over the other's binary mid-assertion.
