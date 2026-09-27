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
| **A13** completion gate | no | `L/mold_compatibility.spl`; `test/01_unit/os/memory/mold_linker_spec.spl`; `test/unit/os/memory/mold_linker_spec.spl` | G6 | Publish the verified `mold_completion_receipt.v2` aggregate after every platform/corpus/performance receipt exists; the predicate computes from its strict digest-bound rows | red: missing, partial, malformed, or symlinked aggregate remains `false`; complete verified aggregate → `true` | sonnet |

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
2. the Windows x86_64 COFF/PE engine links and runs the execution corpus without delegating to `lld-link`/`link.exe`;
3. the full compiler corpus (A5 row "full compiler release") links internally and the execution corpus passes;
4. fast/bounded output digests match for the same request (G3);
5. SimpleOS x86_64 + arm64 kernels boot from `BootLayoutPlan` output on real firmware and a board (or a dated board-blocked record exists) (G4).
Mach-O completion extends `mold_compatibility_features`; Windows COFF is now a completion gate. Both `mold_linker_spec.spl` mirrors flip in the same commit (A13).

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
| A7 slice 2 | **pass** after a Fable blocker (GOTPCRELX relax on undefined-weak/ABS; shell chmod) | Static GOT, static PIE and dynamic libc exec/PIE on aarch64 all run (exit 42, "hi from libc"); x86_64 static under qemu. `readelf -l -S -d -r` parity with ld.lld. `SIMPLE_LINKER=internal` runs `internal:elf` through `link_request_to_native`; the default path is unchanged. `SHN_COMMON` tentative definitions coalesce into deterministic `.bss`, including boot/SimpleOS `*(COMMON)`. x86_64 dynamic image construction is admitted through the production API; imported object references receive aligned executable storage, defined/hashable `.dynsym` entries, and `R_*_COPY`. Explicit GNU-versioned imports retain their version identity through DSO resolution and emit `.gnu.version`, `.gnu.version_r`, and `DT_VER*` metadata. Dynamic metadata/arrays/GOT receive `PT_GNU_RELRO`. `.tdata`/`.tbss` retain `SHF_TLS` and receive a size/alignment-correct `PT_TLS`; x86_64 local-exec `R_X86_64_TPOFF32` resolves against the TLS block end, initial-exec `R_X86_64_GOTTPOFF` uses a GOT slot with `R_X86_64_TPOFF64`, canonical global-dynamic TLSGD and TLSDESC sequences relax to initial-exec without a resolver PLT, and canonical local-dynamic TLSLD/DTPOFF32 sequences relax to local-exec. Every internal ELF image carries a GNU SHA-1 build-id note and `PT_NOTE`, computed over the complete image with the descriptor zeroed. zR/pcrel-sdata4 FDEs are sorted into `.eh_frame_hdr` and exposed through `PT_GNU_EH_FRAME`; unsupported CIE encodings fail closed. Entry, retained-symbol, constructor/destructor, and GNU-retain roots drive relocation-graph section GC; dead-section undefined references do not poison the link. FDE-level compaction drops dead unwind records, rewrites their CIE back-references and relocation offsets, and prevents unwind metadata from retaining dead code. Other TLS models remain named unsupported. Native execution remains a certification receipt. Bug filed: `nogc_sync_mut file_set_mode` is a no-op stub |
| A9 boot layout | **rung 2** (Fable pass) | All 50 in-tree `.ld` parse and round-trip; BootLayoutPlan built for all 6 SimpleOS arch scripts. Rung 3 needs `elf_exec_writer` VMA/LMA/PHDRS support (next). Board blocked (record filed). The real-firmware gate baseline boots hello via EDK2 → Limine |
| A11 conformance | **pass** (Fable) | `check-link-mutation-gates.shs`: 7/7 mutations turn their spec red on the merged tree; selftest runs in CI. Timing on the fixtures: internal ~0.37 s / 150 MB (seed interpreter) vs ld.lld/mold <10 ms / ~20 MB |

Next: A9 rung 3 (BootLayoutPlan in the ELF writer + `ld.lld -T` parity), `link_to_native` routing for `internal` (native_linking owner), RELRO and `.gnu.hash`, x86_64 PLT, and running the engine natively instead of in the interpreter for speed.

## 12. Lane status — 2026-09-19 (third wave: B1/B2/B3)

| Lane | Result | Evidence |
|---|---|---|
| B1 A9 rung 3 (`elf_boot_link`) | **pass** after 2 Fable blockers | Round 1 fixed: ASSERT used the wrong operator precedence (`1<2 && 5<3` was true); `AT>` was ignored; there were no VMA/LMA/PT_LOAD overlap or MEMORY-overflow rejects. Round 2 fixed: a region used as both `>` and `AT>` advanced twice; a NOBITS `AT>` did not advance its region; an explicit address was moved by `ALIGN()`; MIN/MAX and `/` `%` were signed. Each fix has a red→green spec, matched against ld.lld 23: `elf_boot_link` 25/25, `boot_layout_ops` 17/17 (both trees). The hello kernel's loaded bytes are identical to `ld.lld -O0 --no-relax`. **Rung 4 PARTIAL:** EDK2→Limine boots both kernels, and their serial logs are byte-identical. The gate still FAILs for both, because it needs full-kernel `[BOOT]` markers. The sha256 evidence is local-only (`build/os/b1/`). The board is blocked (record updated) |
| B2 ELF extras | **pass** (Fable) | `.gnu.hash` is byte-identical to the ld.lld oracle; `.symtab`/`.strtab` and `PT_GNU_RELRO` are emitted; x86_64 dynamic PLT/GOT has structural parity and is admitted by `elf_link`; non-PIE imported function addresses receive canonical PLT entries and imported objects receive COPY relocations. Native execution certification is still pending. `elf_gnu_hash` 6/6, `elf_symtab` 6/6, `elf_x64_dynamic` 11/11 |
| B3 `link_to_native` routing | **pass** after a Fable blocker (config fields silently dropped) | `SIMPLE_LINKER=internal` routes `link_to_native` to `internal:elf` through a helper shared with `link_request_to_native`. Runtime archives plus user archive/shared-library inputs are consumed; `strip_output` selects symbol-table-free ELF/SimpleOS output and is naturally satisfied by PE output. Hosted ELF `retained_symbols` seed archive closure like `-u/--undefined`; Windows roots similarly drive `.lib`/short-import selection like `/INCLUDE`; SimpleOS validates roots and uses them as section-GC roots when requested. Missing roots fail by name. Fields without implementations are rejected by name. The single-SMF `create_temp_dir` Result bug is fixed; the default path is unchanged |

Merged tree: 27/27 linker specs green; `check-link-mutation-gates.shs` PASS (7/7).

Next: remaining TLS relocation models beyond local/initial-exec, a full-kernel rung 4 (the real gate markers), the x86_64 dynamic execution proof, and native (non-interpreted) engine speed. Exact `SHF_MERGE` pooling now matches the lld `-O1` duplicate-string and aligned `.rodata.cst8` oracles, including symbol/addend remapping. Installed Mold and lld both retain non-identical suffix strings, so tail folding is not part of the compatibility contract. Cross-object `R_X86_64_PC64` now patches the complete signed `S + A - P` value and is pinned by an ld.lld 23.1 fixture oracle. Explicit `R_X86_64_GOTPC32` now resolves the linker-synthesized `_GLOBAL_OFFSET_TABLE_`: hosted ELF emits lld-compatible `.got.plt` storage and the SimpleOS boot path emits a minimal `.got`, with mirrored fixture-backed tests. AArch64 now applies the canonical initial-exec ADR_GOTTPREL_PAGE21/LD64_GOTTPREL_LO12_NC pair and local-exec ADD_TPREL_HI12/LO12 pair, including variant-I TCB bias, checked immediates, GOT TPREL values, and `R_AARCH64_TLS_TPREL64` dynamic relocations.

`R_X86_64_GOT32` now allocates a GOT slot and writes the checked signed
`G + A` offset from `_GLOBAL_OFFSET_TABLE_`: hosted ELF uses its `.got.plt`
base while SimpleOS uses the minimal `.got` base. A checked-in Clang object and
an ld.lld 23.1 oracle pin the negative hosted offset rather than confusing it
with a symbol address or PC-relative displacement.
`R_X86_64_GOT64` follows the same hosted/SimpleOS GOT-base contract without
32-bit truncation; a second Clang fixture pins the sign-extended negative
hosted offset. The installed Windows lld wrote the expected comparison image
and then crashed during teardown, so its emitted bytes are useful oracle
evidence but not a successful lld execution receipt.
`R_X86_64_GOTPCREL64` now allocates a GOT slot and applies the full-width
`G + GOT + A - P` displacement in hosted and SimpleOS links. Clang's `.reloc`
form pins the type-28 object encoding; Mold 2.42 accepts it and provides the
comparison image, while the installed lld 23.1 rejects relocation 28.
`R_X86_64_GOTPC64` now applies full-width `GOT + A - P` directly against the
linker-defined `_GLOBAL_OFFSET_TABLE_` without allocating a per-symbol slot.
Hosted ELF binds that symbol to `.got.plt`; SimpleOS binds it to its minimal
`.got`. A type-29 Clang `.reloc` fixture matches Mold 2.42's emitted value.
`R_X86_64_GOTOFF64` now applies full-width `S + A - GOT` without allocating a
per-symbol GOT slot. Hosted ELF uses the ABI `_GLOBAL_OFFSET_TABLE_` base at
`.got.plt`, while SimpleOS uses its minimal `.got`; a type-25 Clang fixture
matches Mold 2.42's emitted `value - .got.plt` result.
`R_X86_64_PLTOFF64` now applies full-width `L + A - GOT`: local functions use
their definition, imported functions receive a PLT entry, hosted ELF uses its
`.got.plt` base, and SimpleOS uses its minimal `.got`. A type-31 Clang `.reloc`
fixture matches Mold 2.42's emitted value. `R_X86_64_GOTPLT64` remains outside
the compatibility surface because Mold 2.42 rejects relocation type 30.
LLVM 23's `R_X86_64_CODE_4_GOTPCRELX` now follows the non-relaxed signed
32-bit GOT-slot displacement path. A type-43 Clang `.reloc` fixture matches
Mold 2.42 without pretending the ordinary two-byte-prefix relaxation rewrite
also applies to the four-byte-prefix instruction family.
LLVM 23's `R_X86_64_CODE_4_GOTTPOFF` and `R_X86_64_CODE_6_GOTTPOFF` now enter
the existing initial-exec TLS pipeline without an instruction rewrite. They
share a TPOFF GOT slot and apply checked signed PC-relative displacements in
hosted ELF and SimpleOS; a two-relocation fixture matches Mold 2.42's fields
and variant-II `-8` slot value.

`R_X86_64_32S` now rejects values outside `[-2^31, 2^31-1]` instead of
The AArch64 local-exec slice also covers checked and `_NC` TLSLE
LDST8/16/32/64/128 TPREL low-12 relocations, preserving natural scaling and
rejecting misaligned targets.
TLSLE MOVW G2/G1/G0 materialization is also implemented with group-specific
overflow checks and exact instruction-field patching, completing the AArch64
local-exec relocation family represented by LLVM's ABI table.

`R_X86_64_32S` now rejects values outside `[-2^31, 2^31-1]` instead of
silently emitting their low 32 bits, matching mold/lld overflow behavior.
Cross-object `R_X86_64_PC16` and `R_X86_64_PC8` now apply only when their
signed deltas fit, with the successful bytes pinned to an ld.lld 23.1 oracle.
Low-address boot layouts can now apply `R_X86_64_16` and `R_X86_64_8`;
hosted addresses that do not zero-extend from those fields fail by name.
AArch64 `ABS32`, `ABS16`, `PREL32`, and `PREL16` now implement the exact
AAELF64 static-data overflow ranges; this fixes PREL32's former over-wide
positive bound and replaces ABS32 truncation with a named failure.
`R_AARCH64_PLT32` now enters PLT discovery and applies a checked signed
`L + A - P` data relocation, including imported-function PLT addressing.
`R_AARCH64_TSTBR14` and `R_AARCH64_CONDBR19` now enforce four-byte alignment
and architectural reach before patching only their instruction immediate fields.
`R_AARCH64_ADR_PREL_LO21` now patches byte-granular signed ADR deltas while
preserving opcode and destination-register bits and rejecting overflow.
`R_AARCH64_LD_PREL_LO19` now checks literal-load alignment and ±1 MiB reach,
then patches only the instruction's imm19 field.
`R_AARCH64_GOT_LD_PREL19` now allocates a linker GOT slot and applies the same
checked literal-load encoding against the slot address, covering the compact
single-instruction AArch64 GOT access model in addition to ADRP+LDR pairs.
`R_AARCH64_LD64_GOTPAGE_LO15` now supports the medium-GOT sequence by encoding
an aligned 15-bit slot offset from `Page(.got)`. The ELF driver supplies that
page base explicitly and rejects entries outside the ABI's 32 KiB window.
`R_AARCH64_LD64_GOTOFF_LO15` shares the checked LDR field encoding but uses the
exact `.got` start as its base, preserving the ABI distinction when `.got` is
not page-aligned.
The complete AArch64 `MOVW_GOTOFF_G0..G3` family now allocates GOT entries,
applies exact-base offsets, checks the terminal group widths, and preserves
unchecked MOVK opcodes for `_NC` groups.
`R_AARCH64_GOTREL64` and checked signed `GOTREL32` now write direct-symbol
offsets from the synthesized `_GLOBAL_OFFSET_TABLE_` base without allocating
unrelated per-symbol GOT entries.
`R_AARCH64_GOTPCREL32` now allocates the referenced symbol's GOT entry and
writes its checked signed displacement from the relocation place, preserving
the ABI-defined addend instead of applying the zero-addend GDAT rule.
The AArch64 large-model initial-exec `MOVW_GOTTPREL_G1/G0_NC` pair now shares
the TLS-IE GOT allocation path, computes offsets from the exact `.got` base,
and applies the ABI's checked MOVZ/MOVN plus unchecked MOVK encodings.
The complete AArch64 local-dynamic `DTPREL` materialization family now resolves
defined TLS symbols relative to the `PT_TLS` block start, with MOVW, ADD, and
naturally scaled LD/ST encodings for 8/16/32/64/128-bit accesses. Imported or
weak DTPREL references fail closed instead of being assigned a local offset.
Canonical page-based AArch64 TLSGD and TLSLD address-plus-`__tls_get_addr`
sequences now relax before resolution: TLSGD becomes variant-I local-exec
MRS/ADD-high/ADD-low with TPREL relocations, while TLSLD becomes the TLS block
base (`TPIDR_EL0 + 16`) consumed by DTPREL uses. Unpaired, noncanonical, and
undefined-symbol TLSGD sequences fail closed.
The equivalent large-model `MOVW_G1`/`MOVW_G0_NC` TLSGD and TLSLD sequences
share the same checked relaxation, completing both three-instruction address
materialization forms without synthesizing runtime resolver GOT records.
Canonical AArch64 TLSDESC `ADRP/LDR/ADD/BLR` sequences for defined TLS symbols
now relax to variant-I local-exec `MRS/ADD-high/ADD-low/NOP`, removing all four
descriptor relocations and the resolver call. Incomplete, malformed, or
undefined-symbol descriptor sequences fail closed.
The SimpleOS boot-image path now invokes the same pre-resolution TLS relaxer as
hosted ELF. Canonical x86-64 TLSGD and TLSDESC sequences whose symbol is
provided by the static image become initial-exec GOT accesses, and TLSLD plus
DTPOFF32 becomes local-exec; resolver calls are removed before symbol
resolution. The shared AArch64 defined-symbol relaxations are enabled on this
path as well. Imported dynamic TLS and malformed or unsupported sequences
remain fail-closed rather than introducing a runtime TLS resolver dependency.
Linux AArch64 `TLS_DTPREL64`, `TLS_DTPMOD64`, and `TLS_TPREL64` input records
now resolve statically for defined TLS symbols using the `PT_TLS` block start,
main-module ID 1, and variant-I thread-pointer bias respectively. Imported
records now remain as symbol-bound `.rela.dyn` entries for the loader. The
equivalent x86-64 raw `DTPMOD64`, `DTPOFF64`, and `TPOFF64` words use the same
path. Static links and instruction-field imported TLS forms remain fail-closed.
For locally defined x86-64 TLS, those same raw word relocations now use
full-width `S + A` patching: module ID 1, offset from `PT_TLS`, or signed offset
from the thread pointer as selected by the relocation class. They no longer
fall through to an unsupported relocation or a four-byte generic patch.
The AArch64 numeric mapping is pinned to the LLVM/GNU ABI: relocation 1028 is
`TLS_DTPMOD64` and 1029 is `TLS_DTPREL64`; the previously reversed local names
and relocation classes are corrected.
Windows AMD64 COFF now applies `IMAGE_REL_AMD64_SECREL7` with a strict
seven-bit section-relative bound, completing the standard debug/TLS offset family.

The x86_64 local-exec set now includes both instruction-field `TPOFF32` and
data-word `TPOFF64`, with the latter checked against an lld static oracle.
Cross-object `R_X86_64_SIZE32`/`SIZE64` now resolve from the winning definition's
extent rather than the undefined reference row's zero size, also checked against lld.
The SimpleOS boot linker now applies the same winning-definition rule instead
of accidentally encoding the symbol address for these already-classified
relocations.
Hosted ELF and SimpleOS boot relocation collection now share explicit patch
width/range validation across x86-64, ARM32, AArch64, and RISC-V widths. Patches
that cross an input-section boundary and boot relocations with an invalid
symbol-table index fail closed before mutation. Named SIZE32/SIZE64 ABI
constants prevent the raw SIZE64 relocation from being mistaken for a
four-byte default before its later formula rewrite.

## 13. Windows/Linux/SimpleOS completion continuation — 2026-09-26

The compatibility predicate is now expressed as explicit receipt inputs instead
of an undocumented literal. It remains fail-closed. The no-argument predicate
reads `build/linker/mold_completion_receipt.v2`, whose strict v2 schema contains
ten fixed-order `key=sha256:<lowercase-64-hex>` rows matching
`MoldCompletionEvidence`. Missing, partial, reordered, duplicated, uppercase,
or malformed rows keep completion false. The aggregate producer is the trust
boundary and must verify each referenced real-run artifact before publishing
its digest; the consumer uses a bounded no-follow regular-file read, and plain
`pass` values are never accepted. Linux is implemented but
not certified and SimpleOS is awaiting full boot evidence. Windows now has a
fail-closed freestanding AMD64 COFF parser, relocation core, PE32+ writer, and
`SIMPLE_LINKER=internal` route. Static `.lib` archive closure, COMDAT metadata,
short-import decoding, PE import descriptors, ILT/IAT directories, AMD64 import
thunks, COFF common-symbol `.bss`, and zero-file-byte BSS output are now
implemented. Object `$` subsections are ordered and merged into bounded PE
sections, all standard COMDAT selection modes are handled, undefined and
duplicate externals are rejected before emission, import-directory sizes are
descriptor-exact, and AMD64 `ABSOLUTE`/`SECTION`/`SECREL` join the address
relocations. `ADDR64` sites produce sorted/deduplicated `.reloc` blocks, so
PE ASLR flags are backed by real `IMAGE_REL_BASED_DIR64` records. Relocations
against local or cross-object external `IMAGE_SYM_ABSOLUTE` symbols use the
literal symbol value without PE image-base adjustment; the resolver carries
absolute provenance so indirect `ADDR64` sites also stay out of `.reloc`, and
section-relative relocation kinds reject absolute targets by name. Hosted CRT
completion and native execution evidence
remain open. The user-expanded completion boundary includes
Windows x86_64 and therefore supersedes the earlier statement that COFF did not
gate completion.

The hosted COFF continuation now has a bounded pure parser for compiler-emitted
`.drectve` resolution inputs. It recognizes quoted `/DEFAULTLIB`, `/INCLUDE`,
and `/ALTERNATENAME:weak=default` rows, deduplicates identical requests, rejects
conflicting aliases and malformed owned directives, and collects them only from
sections marked `LNK_INFO`. `/INCLUDE` rows now join explicit retained symbols
as archive-closure roots and fail by name when no object, archive member, or
import satisfies them. `/ALTERNATENAME` chains now participate in the same
archive closure, validation, section-relative lookup, and final relocation
resolution; a real primary definition wins, aliases may target ordinary,
absolute, common, or imported symbols, and cycles fail closed. Native-wrapper
`/DEFAULTLIB` discovery now parses the initial COFF objects before archive
loading, resolves requested libraries through explicit/runtime/MSVC SDK search
paths, deduplicates them with configured support libraries, and fails by
library name when missing. The core now exposes default-library dependencies
from roots plus only the archive members selected by the current closure. The
native wrapper resolves newly reported libraries, adds their archives, and
repeats dependency discovery until stable. Directives in unused members are
not admitted, avoiding false dependencies and missing-library failures.
`/NODEFAULTLIB:name` suppresses case-insensitively with optional `.lib`, while
bare `/NODEFAULTLIB` suppresses all implicit defaults. Directive-owned archives
are recomputed independently of explicit/configured/runtime libraries on each
closure pass; contradictory selected-member policy fails after a bounded
convergence limit rather than oscillating indefinitely.
`/FAILIFMISMATCH:key=value` rows are merged exactly across root objects and
selected archive members before layout. Repeated identical values are accepted,
conflicting values fail closed with the key and values reported, and directives
from unused archive members do not affect the link.

The admitted aggregate producer is
`src/app/test/mold_completion_receipt.spl`. It accepts exactly ten receipt
paths in the fixed `MoldCompletionEvidence` order. Each input must use
`mold-linker-evidence-v1`, name the expected gate, report `status=pass`, and
bind a regular no-follow command transcript and result artifact with lowercase
SHA-256 digests. The producer re-hashes both bound files, reads each receipt
with a 16 KiB limit, and atomically writes the aggregate only after all nine
validate. A digest-shaped text file alone therefore cannot open the gate.

```text
simple run src/app/test/mold_completion_receipt.spl -- \
  <linux-x86-64> <linux-aarch64> <windows-x86-64> <windows-arm64> <compiler-corpus> \
  <digest-parity> <simpleos-x86-64-boot> <simpleos-arm64-boot> \
  <platform-receipts> <performance-gate>
```

Remote interpreter planning now has target-aware binary placement contracts:
Linux `/usr/local/bin/simple`, Windows
`C:\Program Files\Simple\simple.exe`, and SimpleOS `/usr/bin/simple`, with an
explicit `--simple-bin` override and rejection of unknown automatic targets.
The same resolver now owns the real remote-PC adapter command, eliminating its
previous hardcoded `bin/simple` execution path.
The remote-PC adapter can now upload a selected local interpreter to an
explicit staging path and publish it at the target-owned location. Linux and
SimpleOS use a mode-0755 sibling followed by atomic rename; Windows uses a
sibling file and fail-fast PowerShell replacement. Upload or publication
failure is returned as an error rather than running an older remote binary.
Remote publication now requires absolute staging and installed paths and
compares lexical canonical forms before upload. Dot segments, repeated
separators, slash direction, drive-letter case, and Windows path case can no
longer disguise the live destination or its sibling publication file.
Known-target explicit binary paths are also rejected at initial resolution
unless target-absolute, keeping command planning and execution independent of
the remote shell's working directory. POSIX roots, Windows drive roots, and
bare UNC shares are rejected as installed or staging paths because they do not
name a binary file leaf. Windows file leaves also fail early for DOS device
aliases (including extensions), alternate-data-stream syntax, trailing-dot or
trailing-space aliases, and illegal filename characters in every component
after the drive root or UNC share; ASCII control characters are rejected across
the complete path.
UNC server/share syntax is validated separately, and NT extended/device
namespaces (`\\?\\`, `\\.\\`) are rejected as non-file placement roots.
Before transfer, the adapter now asks the remote host to prove that both the
upload leaf and sibling publication leaf are absent, including POSIX symlinks
and Windows reparse entries visible to `Get-Item`. A stale or redirected leaf
therefore fails before `scp`/terminal upload can follow it.
That preflight also requires the staging parent to exist and walks its complete
ancestor chain, rejecting POSIX symlinks, Windows reparse points, and
non-directories before `terminal_upload` runs. Uploads therefore cannot be
redirected through a persistent staging-directory alias.
After the sibling copy and permission step succeeds, publication removes the
uploaded staging leaf before the atomic replacement, so a successful install
does not poison the next absence preflight.
Between upload and publication, the adapter hashes the selected local binary
and requires the remote staging file to match that lowercase SHA-256. Linux
and SimpleOS use `sha256sum`; Windows uses `Get-FileHash`. Missing hash tools,
read failures, malformed local digests, or byte mismatches stop publication.
Both that digest step and the publication command recheck that the upload leaf
is still a regular non-symlink/non-reparse file before reading it. A swapped
directory, POSIX symlink, or Windows reparse entry therefore fails before its
target can be hashed or copied into the publication sibling.
After creating the destination directory, publication walks every parent up
to the filesystem root and rejects POSIX symlinks, Windows reparse points, and
non-directory components before opening the sibling file. Persistent parent
redirection therefore cannot move an otherwise valid install outside the
configured target tree.
The publication command carries the same digest and re-hashes the sibling copy
after mode changes but before rename. A copy mismatch removes that sibling and
leaves the installed interpreter untouched.
After the atomic replacement, the adapter independently revalidates that the
live destination is a regular non-symlink/non-reparse file and that its SHA-256
still matches the selected local interpreter. A final-path mismatch stops the
remote run without deleting the destination, preserving evidence and avoiding
an unsafe cleanup of a path that may have changed ownership after publication.
The final verifier also walks the installed path's complete ancestor chain;
a directory swapped to a POSIX symlink or Windows reparse point after
publication therefore cannot satisfy verification through a redirected copy.
Windows publication no longer relies on `Move-Item -Force`: an existing file
is replaced with sibling-volume `System.IO.File.Replace`, an absent path uses
`File.Move`, and a reparse point or non-file destination fails closed before
the staged upload is consumed. The sibling is created through
`FileMode.CreateNew`, so a post-preflight leaf cannot be overwritten. This
preserves the old binary until the verified candidate is atomically committed.
Linux and SimpleOS publication now reject symlink and non-regular installed
leaves, create the sibling under shell noclobber mode before copying into that
owned regular file, and use `mv -T`, preventing a raced sibling or destination
directory from redirecting publication.
POSIX parent-directory creation is rendered from the already validated
destination path and quoted independently. It no longer uses an unquoted
`$(dirname ...)` result, so explicit install parents containing whitespace,
apostrophes, or glob metacharacters cannot be split or expanded by the shell.
The terminal layer now backs agent/public-key remote placement with bounded
host OpenSSH `ssh`/`scp` processes because its legacy SSH SFFI externs have no
runtime definitions. Connection probes, command execution, upload, and
download are functional without a fabricated session; password auth and
interactive channels remain explicitly fail-closed.
Post-guard placement failures now run a target-owned cleanup command after a
partial upload, staging digest mismatch, or failed publication. Cleanup is
idempotent for a missing leaf and removes only a regular staging file; POSIX
symlinks/non-files and Windows directories/reparse points are refused with a
named error rather than followed or deleted. This prevents an owned failed
upload from poisoning the next absence preflight without turning cleanup into
an attacker-controlled deletion primitive.
Failed publication also cleans the separately owned `.remote-test-new`
sibling before cleaning the upload leaf. That cleanup is likewise idempotent
and regular-file-only, so copy, permission, hashing, or final-rename failures
cannot permanently poison the next two-leaf absence preflight.
When either cleanup leaf exists, cleanup now validates its complete parent
chain with the same POSIX symlink and Windows reparse-point policy before
deletion. Missing leaves remain idempotent success, while a redirected parent
fails closed instead of deleting a regular file outside the owned tree.
The adjacent Arm32/RiscV32 compiler bridge no longer returns successful fixed
return-zero byte sequences while ignoring source. It now fails closed until a
real source-derived target backend is connected. The native RV32 backend now
exposes a raw instruction-image entry point, distinct from its ELF32 object
entry point, so the remote compiler adapter can upload source-derived bytes at
the target-selected code base without leaking container headers into target
memory. The compiler-owned RV32 adapter now composes the canonical frontend,
HIR and target-specific MIR lowering with that raw backend. It resolves
internal `R_RISCV_CALL_PLT` AUIPC/JALR pairs against the placed image and fails
closed on undefined, malformed, or unsupported relocations. RV32 QEMU/GHDL
integration lanes use this real source compiler. The Arm32 backend remains an
explicit completion gap; remote placement itself is wired. The linker
relocation layer now recognizes `EM_ARM` and applies the foundational AAELF32
`NONE`, `ABS32`, `REL32`, `PC24`, `CALL`, and `JUMP24` formulas with checked
range/alignment and opcode-preserving ARM branch patching. Thumb-2 `THM_CALL`,
`THM_JUMP24`, and absolute/PC-relative `THM_MOVW`/`THM_MOVT` records are also
encoded with checked signed branch reach and split-immediate preservation.
The shared ELF object parser now accepts little-endian ELF32 headers and
section tables, decodes ELF32 symbols, and canonicalizes both REL and RELA
records into the same symbol/type representation used by ELF64. Implicit REL
addends are decoded from ARM data words, ARM branch immediates, Thumb-2 branch
pairs, and split Thumb MOVW/MOVT instructions during object admission; malformed
fields and unsupported ARM REL types fail closed. ARM-state MOVW/MOVT, V4BX,
and signed PREL31 compact-unwind references are also decoded and applied, with
PREL31 preserving its high compact-model flag bit. A deterministic ARM32 raw
image linker now lays out allocatable PROGBITS/NOBITS sections from ELF32 ARM
objects, resolves local/global/weak symbols across inputs, preserves Thumb entry
bits, applies the shared ARM relocation engine, and rejects
unsupported allocatable sections, malformed bounds, undefined strong symbols,
and duplicate strong definitions. This connects parsed LLVM-style ARM32 objects
to the raw-image boundary required by remote and bare-metal placement. The
raw linker now also coalesces `SHN_COMMON` tentative definitions into one
zero-filled tail allocation per name, selecting maximum size/alignment in
encounter order. Strong section definitions suppress tentative storage, weak
section definitions yield to strong commons, and malformed non-power-of-two
alignment fails before image mutation.
raw path also decodes and applies narrow Thumb-1 `R_ARM_THM_JUMP11` and
`R_ARM_THM_JUMP8` REL branches with signed range checks while preserving their
opcode and condition fields. Width-correct `R_ARM_ABS8`/`R_ARM_ABS16` data
relocations and bare-metal-default `R_ARM_TARGET1` (`ABS32`) are also admitted
with signed-or-unsigned overflow checks. `R_ARM_THM_PC8` now decodes the
AAELF32 wrap-adjusted REL addend and patches LDR-literal/ADR immediates from
`S + A - (P & ~3)` with alignment and range checks. Raw-image bounds validation
uses each relocation's actual one-, two-, or four-byte field width, so a narrow
Thumb relocation may occupy the final halfword of an input section. The
natural LLVM Cortex-M3 `R_ARM_THM_PC12` literal-load form is also decoded and
patched with its signed U-bit/magnitude encoding and checked 12-bit reach; both
forms have checked-in ELF32 oracle objects. The remaining relocation corpus,
hosted ARM executable emission, and real target
execution evidence remain open.
The ARM32 raw-image integration corpus now also includes two LLVM-compiled C
objects. Their real `THM_MOVW_ABS_NC`/`THM_MOVT_ABS`, `THM_JUMP24`, and
`PREL31` records pass together through ELF32 parsing, cross-object resolution,
layout, relocation, and final image construction at the remote code base.

The compiler-owned ARM32 remote adapter now performs the full source-to-image
composition: frontend and target-aware MIR lowering, explicit Thumbv7-M
Cortex-M3 LLVM object emission, ELF32 ARM raw linking at the requested target
address, entry-placement validation, and checked byte conversion. QEMU ARM,
STM32H7, and STM32WB integration/system lanes now call this adapter directly;
the prior STM32H7 fixed `movs r0, #0` compiler stub and stale calls through the
compiler-independent fail-closed `CompilerBridge` are removed. ARM exception
index sections are admitted as allocatable file-backed data. Real QEMU/hardware
execution receipts, broader object/relocation coverage, and hosted executable
emission remain open.

The ARM adapter audit found a shared LLVM object-emission blocker before target
linking: `OptimizationLevel.Size` was passed to `llc` as `-Oz`, although `llc`
accepts only numeric `-O0` through `-O3` code-generation levels. All three llc
object paths now use one tested policy (`Size` -> `-O2`; size-oriented IR
optimization remains owned by `opt -Os/-Oz`). The installed Windows llc then
reached target selection but reported that its build has no Thumb/ARM target,
so ARM object/runtime evidence still requires an LLVM distribution with that
backend plus QEMU/target GDB or hardware.

Implemented source slice:

- raw AMD64/ARM64 COFF object decoding with section, primary/aux symbol, long
  name, BSS, and relocation bounds checks. Classic 20-byte COFF headers and
  anonymous 56-byte bigobj headers share the same bounded parser; bigobj uses
  20-byte symbols, signed 32-bit section numbers, and the high half of
  associative COMDAT section indices rather than truncating them to classic
  COFF widths. A zero symbol count now requires the header's symbol-table
  pointer to be zero, preventing malformed objects from supplying a phantom
  string-table base. Archive admission recognizes the bigobj class identifier rather
  than skipping its machine-zero prefix, and short-import detection explicitly
  excludes bigobj members despite their shared `0/0xffff` signature. Sections
  using `IMAGE_SCN_LNK_NRELOC_OVFL` decode the first relocation record as the
  extended count marker, validate its reserved fields, and expose only the real
  relocation rows downstream. Merged `$` subsections preserve each input
  section's encoded power-of-two alignment against its absolute RVA, including
  zero-filled padding and the legal 8 KiB maximum when the group begins on a
  4 KiB PE boundary, and reject the reserved alignment encoding rather than
  silently weakening it;
- AMD64 `ADDR64`, `ADDR32`, `ADDR32NB`, and `REL32..REL32_5` formulas with
  truncation rejection;
- ARM64 `ADDR32`, `ADDR32NB`, `BRANCH26`, `PAGEBASE_REL21`, `REL21`,
  `PAGEOFFSET_12A`, and `PAGEOFFSET_12L` relocation patching with opcode,
  alignment, and range validation. A reproducible real Clang ARM64 COFF object
  pins the compiler-emitted relocation census. The deterministic PE32+ writer
  now emits either AMD64 or ARM64 machine headers through a checked target
  parameter while preserving the AMD64 compatibility wrapper, and ordinary
  ARM64 COFF members are admitted by the archive-closure parser. ARM64 `.pdata`
  validation and sorting uses its native 8-byte runtime-function rows rather
  than the AMD64 12-byte format. Shared link preparation now validates an
  explicit target machine, and symbol/export/relocation address resolution
  consumes an explicit image base instead of embedding the AMD64 constant.
  Microsoft short-import decoding admits both AMD64 and ARM64 machine rows
  while preserving the machine for architecture-specific thunk selection.
  ARM64 code imports now synthesize checked 12-byte `ADRP x16` / `LDR x16` /
  `BR x16` stubs against 8-byte-aligned IAT slots; mixed-machine imports and
  out-of-range page deltas fail closed.
  The shared COFF linker now exposes an ARM64 PE32+ route selecting ARM64
  object/archive validation, relocation formulas, imports, exception sorting,
  image base, and machine header; ARM64 `SECREL` is resolved against the merged
  output-section base. The remaining specified native ARM64 relocation forms
  are covered too: 64-bit VA with DIR64 base-relocation publication, `SECTION`,
  low/high section-relative ADD/LDR immediates, conditional and test-bit
  branches, and signed `REL32`; CLR `TOKEN` remains outside the native
  executable contract. A hand-built ARM64 COFF integration corpus drives these
  forms through parsing, symbol resolution, relocation dispatch, PE emission,
  and DIR64 directory publication rather than testing formulas alone. Windows
  native routing now derives the architecture from
  the explicit target triple or normalized host architecture, selects the ARM64
  internal linker/default-library scan, and passes `/MACHINE:ARM64` through the
  external MSVC path. Native Windows-on-ARM execution and full SDK/CRT corpus
  evidence remain open, so this route is not yet certified;
- deterministic PE32+ section/image writer with import, exception, and base
  relocation directories, including synthesized DIR64 page blocks;
- AMD64 multi-object symbol resolution, static `.lib` fixpoint extraction,
  COMDAT selection metadata with fail-closed unsupported replacement modes,
  Microsoft short-import decoding plus `.idata`/IAT/thunk synthesis, and both
  GNU and MSVC Windows `SIMPLE_LINKER=internal` routing without external
  fallback;
- Windows SDK/CRT search-root discovery plus demand-driven system and
  `simple_native_all` import-library closure for hosted runtime archives;
- specification-defined COFF weak externals: `NOLIBRARY` and `ALIAS` resolve
  directly through their fallback, while `LIBRARY` prefers an ordinary or
  short-import archive provider for the primary and falls back only when no
  library advertises one; unknown policies remain fail-closed;
- AMD64 static TLS directory publication from the CRT-defined `_tls_used`
  memory image: PE data-directory row 9 points at the resolved, relocated
  40-byte `IMAGE_TLS_DIRECTORY64`; `.tls$*` data without that file-backed
  directory fails closed instead of producing an image the Windows loader
  cannot initialize. Dollar-subsection grouping now applies even when the raw
  COFF name already fits eight bytes, so `.tls$*`, `.CRT$*`, and short
  `.text$*` names merge and sort under their base output section;
- CRT loader metadata is now retained from otherwise-unreferenced archive
  members when `_tls_used` or `_load_config_used` is advertised. A resolved
  load-config structure publishes PE data-directory row 10 using its leading
  declared `Size`; truncated, zero-sized, or non-file-backed structures fail
  closed before image emission;
- merged AMD64 `.pdata` is validated as complete 12-byte `RUNTIME_FUNCTION`
  rows and sorted by relocated `BeginAddress` before PE emission, as required
  by the Windows x64 unwinder. Truncated rows and non-increasing function ranges
  fail closed; data-directory row 3 covers the sorted table;
- `.rsrc$*` inputs merge into `.rsrc`, undergo bounded validation of directory
  nodes, UTF-16 names, leaf records, cycles, reserved fields, and file-backed
  payload ranges, then publish PE data-directory row 2. Malformed resource
  objects cannot produce a loader-visible resource directory;
- `.edata$*` inputs merge into `.edata`; the relocated export directory now
  receives bounded validation of its DLL name, export-address table, name
  pointer table, ordinal table, and NUL-terminated names before PE
  data-directory row 0 is published. Truncated tables and out-of-range name
  ordinals fail closed;
- `/EXPORT:name[=internal]` directives now retain archive providers and
  synthesize deterministic `.edata` tables. Explicit ordinals, `NONAME`,
  `DATA`, and `PRIVATE` are parsed as typed policy; duplicate ordinals,
  conflicting declarations, missing targets, absolute targets, malformed
  options, and mixed prebuilt/synthesized export directories fail closed;
- object-only CodeView `.debug$*` streams are discarded from internal PE
  images instead of being treated as loadable sections. `debug=true` remains a
  named unsupported policy until PDB and PE debug-directory production exist;
- host-independent SimpleOS x86_64/arm64 routing through the existing
  `BootLayoutPlan` + `elf_boot_link` engine.

LLVM COFF oracle evidence on this Windows host confirms the parser model against
a real Clang object (`IMAGE_FILE_MACHINE_AMD64`, eight sections, long
`.llvm_addrsig`, zero-file-byte `.bss`, primary+aux symbols, `REL32` and
`ADDR32NB`). A checked-in two-object Clang corpus now exercises the production
COFF link through COMDAT selection, cross-object `REL32`, `.xdata`, relocated
and sorted `.pdata`, entry resolution, writable data, and PE32+ emission;
`lld-link` provides the independent entry/section/exception-directory oracle.
Executable Simple specs remain `TEST_BLOCKED`: neither this clean
worktree nor the shared checkout has an admitted Stage 2/3 or deployed Stage 4
pure-Simple binary, and the Rust seed is bootstrap-only.
The canonical Windows-GNU Stage-2 bootstrap now publishes all four immutable
Rust authority artifacts and passes the 5/5 authority preflight. With
`--backend=cranelift`, one build entered the pure-Simple Stage-2 compilation
and reached approximately 9.8 GiB RSS before Windows commit pressure ended it
with `memory allocation of 270352 bytes failed`; it did not reach the linker
and produced no admitted compiler. This replaces the earlier transient-status
125 fingerprint blocker with a measured memory blocker.

The Stage-2 sealed environment now sets `MIMALLOC_ARENA_EAGER_COMMIT=0`,
`MIMALLOC_PURGE_DELAY=0`, and `MIMALLOC_PURGE_DECOMMITS=1`, includes those
bindings in the command digest, and admits their names through the fail-closed
canonical transcript contract. A focused contract test proves one binding in
the digest and one in execution, preventing the duplicate assignment that
caused the first pre-exec refusal. The required rerun is deferred: this session
used its three allowed verify/fix cycles, so no fourth canonical bootstrap was
started. Full Windows native execution, Linux certification, SimpleOS full
boot, and performance receipts remain open; consequently the completion
predicate correctly remains false.

Linux internal routing no longer rejects `runtime_path`, `runtime_bundle`,
`libraries`, or `library_paths`. The selected admitted runtime provider is
added as archive input and named user libraries resolve dynamic-first across
explicit, CRT, and architecture-default search paths. Only real ar archives
and ELF `ET_DYN` inputs are accepted; GNU ld text scripts are skipped during
name lookup and explicit non-binary inputs fail closed. Typed `-rpath` and
`-Wl,-rpath,` extra flags now become one ordered, deduplicated `DT_RUNPATH`
payload in `.dynstr`, admitting Stage-4 `$ORIGIN` and provider-directory
placement. Malformed rpaths and every unmodelled extra flag still fail closed;
debug policy remains unsupported until its output semantics are implemented.
Linux internal routing also accepts explicit `--eh-frame-hdr`, `--build-id`,
`--build-id=sha1`, and `--gc-sections` requests because those exact policies
are intrinsic to every produced image. Alternate build-id algorithms and
`--no-gc-sections` remain rejected rather than silently changing semantics.
GNU `-z relro` spellings are accepted because dynamic metadata and GOT ranges
already receive `PT_GNU_RELRO`. GNU `-z now` spellings now select typed eager
binding and emit `DT_BIND_NOW`, `DF_BIND_NOW`, and `DF_1_NOW`; lazy binding
remains the default and unmodeled `-z` policies fail closed.
Hosted ELF and Windows retained-symbol roots seed
archive extraction; SimpleOS validates roots against its object and script
definitions and retains their section graph under `--gc-sections`; every route
fails unresolved roots by name. `strip_output`
is implemented across internal ELF, SimpleOS, and PE routing rather than being
silently ignored.

SimpleOS boot linking now preserves `SHF_TLS`, requires TLS output sections to
form one contiguous image, and emits an overlapping read-only `PT_TLS` header
whose file size excludes `.tbss` while its memory size includes zero-fill.
The static boot model resolves module ID 1 plus local-dynamic and local-exec
offsets for x86-64 variant II and AArch64 variant I; x86 `TPOFF32` is lowered
through the signed 32-bit relocation path while `TPOFF64` remains full-width.
Initial-exec references to locally defined TLS now allocate distinct GOT slots
containing x86-64 variant-II or AArch64 variant-I TPREL values; x86-64
`GOTTPOFF` and AArch64 ADR/LD and MOVW TLSIE forms resolve through those slots.
Undefined imported/dynamic TLS and unsupported instruction forms remain
explicit errors. This closes the structural linker slice, but not the open
SimpleOS x86-64/arm64 full-boot or performance evidence gates.

The SimpleOS internal route now consumes the selected admitted runtime bundle,
explicit static libraries, and library search paths. Boot linking performs the
same symbol-driven archive fixpoint used by hosted ELF, including transitive
members and entry/retained-symbol roots, while preserving archive member names
in diagnostics. Shared objects remain invalid for a freestanding boot image;
missing libraries, malformed archives, and incomplete named runtime providers
fail before publication. `debug` and unmodelled `extra_flags` remain explicit
unsupported policy rather than being ignored.

Modeled SimpleOS `extra_flags` now project GNU `-T`/`--script` spellings into
the BootLayoutPlan script input, `--defsym=name=expression` into typed
post-layout symbol assignments, and `--gc-sections` into relocation-graph
collection rooted by the entry, retained symbols, `SHF_GNU_RETAIN`, lifecycle
arrays, and script `KEEP` patterns. Dead unwind FDEs are compacted through the
shared hosted-ELF collector, dead-section undefined references do not poison
the boot link, and live common symbols remain placeable through `*(COMMON)`.
The route also consumes `-nostdlib`, `-static`/`-Bstatic`, balanced archive
group markers, and `--no-gc-sections` as typed policy: the boot engine is
intrinsically freestanding/static, archive extraction is already a fixpoint,
and the last GC toggle wins. GNU `--wrap=name` now rewrites undefined `name`
references to `__wrap_name` and `__real_name` references back to `name` through
one shared projection used before both archive fixpoint extraction and final
resolution; definitions retain their real names. This admits the canonical
x86-64 module-initializer wrapper without hiding a missing wrapper provider.
Duplicate identical policy is deduplicated; conflicting scripts, conflicting
symbol expressions, malformed values, and every unmodeled flag fail closed.
An explicit flag and `SIMPLE_LINKER_SCRIPT` must name the same script when both
are present.

The production LLVM SimpleOS entrypoints no longer bypass this route when the
user selects `SIMPLE_LINKER=internal`. ARM64 freestanding images, canonical
x86-64 userspace images (including sysroot archives and module-init wrapping),
and legacy x86-64 kernel images call one host-independent
`link_simpleos_internal` facade with their exact objects and typed policy.
Their default path still invokes external `ld.lld`; RISC-V remains on its
separate unsupported internal-linker lane. Mirrored
`simpleos_internal_production_routing_spec.spl` contracts pin all three
supported branches, the x86 sysroot archives/wrapper, and preservation of the
default external fallback.

Remote interpreter placement now validates the exact path bytes later quoted
into target commands. Known-target explicit and staging paths reject outer
whitespace instead of validating a trimmed alias and executing the original;
POSIX normalization no longer treats backslash as a directory separator, and
control-character paths fail before transfer. The independent staging-digest
command now applies the same absolute-file-leaf policy, including Windows
device/namespace rejection, so it cannot hash a root or a different lexical
target than the publication pipeline.

The 2026-09-27 native Windows bootstrap probe used the canonical
`bootstrap-windows.sh --msvc --backend=cranelift --full-bootstrap
--stop-after-stage2 --jobs=1` lane with `SIMPLE_LINKER=internal`. It passed
Windows materialization, disk, platform, fingerprint, and Cranelift preflight,
then stopped before the Simple linker while building the Rust authority seed:
`ring` could not find the MSVC/UCRT `assert.h`. The repository's canonical
`windows-msvc-bootstrap-env.shs` confirmed the host has no discoverable Visual
Studio C++ workload (`vswhere.exe` absent) and therefore cannot supply the VC
and Windows SDK include/library roots. No linker verdict or admitted Stage 2
was produced. The next Windows execution gate requires a host with the VS 2022
Desktop C++ workload and Windows SDK; this environmental block does not change
the false completion predicate.

The internal Windows route now consumes case-insensitive `/SUBSYSTEM:CONSOLE`
and `/SUBSYSTEM:WINDOWS`, `/STACK:reserve[,commit]`, and
`/HEAP:reserve[,commit]` as typed PE32+ image policy. It also consumes the
production toolchain's `/MACHINE:X64` or `/MACHINE:ARM64` flag as a typed
validation against the selected target, rejecting cross-architecture policy
instead of ignoring it. `/ENTRY:symbol` is carried unchanged into archive
closure, selected-member default-library discovery, and final relocation, so a
custom CRT entry is not replaced by the automatic entry heuristic. Identical
entry requests deduplicate; empty, conflicting, whitespace/control-bearing
entries fail closed. `/BASE:address` now drives symbol addresses, address-based
relocations, and the emitted PE32+ image base through one value; it requires a
positive 64 KiB-aligned address with 4 GiB headroom, deduplicates equivalent
decimal/hex spellings, and rejects conflicting or unsafe bases. The route also
models `/DYNAMICBASE`, `/HIGHENTROPYVA`, `/NXCOMPAT`,
`/LARGEADDRESSAWARE`, and `/TSAWARE`, including each `:NO` spelling. These
drive the PE file/DLL characteristic bits; ASLR/high-entropy bits remain absent
without a relocation directory, explicit high entropy without dynamic base is
rejected, and conflicting repeats fail closed. `/FIXED` now suppresses the
otherwise synthesized base-relocation directory, marks relocations stripped,
and disables dynamic-base/high-entropy policy; explicitly requesting either
ASLR policy with `/FIXED`, or mixing `/FIXED` with `/FIXED:NO`, fails closed.
`/FIXED:NO` retains relocations and the existing ASLR defaults. Decimal and `0x` values
are bounds-checked, identical duplicate policy is harmless, and conflicting,
zero, overflowing, commit-over-reserve, malformed, or unmodeled flags fail
before publication. The PE writer validates the policy and emits its subsystem,
stack, and heap fields for both AMD64 and ARM64; legacy callers retain the
byte-identical console/1 MiB reserve/4 KiB commit defaults. Mirrored contracts
check parser rejection and the exact optional-header bytes. The internal route
also consumes `/ALIGN` and `/FILEALIGN` as one typed layout policy. COFF output
section RVAs, synthesized import/export/relocation sections, PE header/image
sizes, raw offsets, padding, and optional-header fields all use the selected
values. Section alignment is a bounded power of two from 512 bytes through 256 MiB;
file alignment is a power of two from 512 bytes through 64 KiB and cannot exceed
section alignment; a sub-page section alignment must equal file alignment.
Duplicate equal values deduplicate and conflicts fail closed.
`/OSVERSION:major[.minor]`, `/VERSION:major[.minor]`, and the optional
`,major[.minor]` suffix on `/SUBSYSTEM` now populate the six corresponding
PE32+ optional-header fields. Components are decimal or `0x` values bounded to
16 bits; malformed, overflowing, and conflicting repeats fail before output.
Defaults remain OS 6.0, image 0.0, and subsystem 6.0 for byte compatibility.
`/OPT:REF` now drives relocation-graph COMDAT elimination. Entry candidates,
`/INCLUDE` roots, exports, and every ordinary non-COMDAT section seed the live
graph; relocations and associative COMDAT parentage retain reachable packaged
sections, while undefined references owned only by discarded sections do not
poison the link. `/OPT:NOREF` preserves all selected sections, and conflicting
REF policy fails closed.
`/OPT:ICF` now folds live COMDATs only when their bytes, virtual size, complete
section characteristics, output class, alignment, relocation sites/types, and
resolved relocation identities match. The conservative identity rule declines
self-recursive or merely structurally similar graphs instead of risking an
incorrect address merge. `/OPT:NOICF`, combined `/OPT:REF,ICF`, and conflict
validation are typed through both AMD64 and ARM64 production routes.
Command-line `/DEFAULTLIB:name`, `/NODEFAULTLIB[:name]`, and
`/INCLUDE:symbol` now share the archive-closure and retained-root path used by
object directives. Library suppression is case-insensitive and treats the
optional `.lib` suffix canonically; bare `/NODEFAULTLIB` suppresses directive
and command-line defaults without removing explicitly supplied libraries.
Command-line `/EXPORT:public[=internal][,@ordinal][,NONAME][,DATA][,PRIVATE]`
now uses the same typed parser, conflict checks, archive roots, and `.edata`
builder as object-embedded directives on both AMD64 and ARM64 routes.
The production `allow_duplicate_definitions` policy now reaches internal COFF
as deterministic `/FORCE:MULTIPLE` semantics: the first external definition
in input/archive order wins and later definitions become references to it.
An explicit case-insensitive `/FORCE:MULTIPLE` selects the same typed path.
Bare `/FORCE` and `/FORCE:UNRESOLVED` remain fail-closed because emitting an
image with unresolved references is not an admitted internal-linker policy.
Strict COFF APIs still reject duplicates unless that policy is explicitly set.
The internal route also consumes `/NOLOGO`, `/DEBUG:NONE`, `/INCREMENTAL:NO`,
and `/MANIFEST:NO`
because it is quiet, emits neither debug/PDB nor manifest directories, and is
always a complete one-shot link. Their enabled counterparts remain named
unsupported until those output contracts are implemented. Native
Windows execution remains pending the host prerequisite recorded above.

Remote placement now requires the selected local interpreter to be a regular
no-follow file before rendering commands, hashing, or uploading it. Local
symlinks, directories, and missing paths therefore cannot become upload
sources; the target-side staging digest still detects replacement after this
local preflight.
Destination creation now walks the nearest existing publication ancestor
before `mkdir -p` or PowerShell `New-Item`, rejecting POSIX symlinks, Windows
reparse points, and non-directories before any filesystem mutation. The
existing post-creation full-chain validation remains as the second phase.

The post-upload digest verifier and publication command now independently walk
the staging file's complete parent chain immediately before reopening it.
POSIX symlink ancestors and Windows reparse/non-directory ancestors therefore
fail closed even when an attacker swaps a staging directory after the initial
absence preflight but before hashing or publication.

The Linux internal route now projects `--hash-style=gnu`, `sysv`, or `both`
into typed ELF layout policy. The selected `.gnu.hash` and/or `.hash` sections
and their matching `DT_GNU_HASH`/`DT_HASH` tags are emitted together; unknown
or conflicting requests fail before publication. Direct linker API callers
retain the byte-compatible `both` default, while the production mold-compatible
command line's existing `--hash-style=gnu` request now produces GNU-only output.
GNU `--strip-all` and `-s` now select the existing typed internal-ELF symbol
table stripping path instead of being rejected as unmodeled flags. Non-default
dynamic hash policy on a static image fails closed rather than being ignored.
GNU `--no-undefined`/`-z defs` are admitted because every unresolved strong
symbol already fails before layout. `-z noexecstack` is admitted with a
fixture-backed assertion that `PT_GNU_STACK` is RW and lacks execute permission;
the opposite undefined/execstack policies remain fail-closed.
GNU `--as-needed` now becomes typed ELF request policy: relocation-selected
provider DSOs and providers named by retained-symbol roots keep one ordered
`DT_NEEDED`, while unused shared libraries are omitted after the complete scan.
The wrapper rejects mixed positional enable/disable flags because its normalized
library list cannot reconstruct their original interleaving; `--no-as-needed`
retains the existing all-input behavior.
Shared objects without `DT_SONAME` now use their preserved linker-input
identity for `DT_NEEDED`, matching GNU/mold behavior instead of rejecting a
valid DSO. An embedded SONAME remains authoritative; searched `-l` inputs use
the resolved file leaf, while explicitly supplied paths retain that path.
Repeated byte-identical shared objects with the same effective SONAME are now
idempotent and emit one dependency. Different payloads advertising the same
SONAME fail closed before resolution, preventing link-time symbols from being
bound to a second image the runtime loader could alias to the first SONAME.
The DSO export reader now honors the low two `st_other` visibility bits:
DEFAULT and PROTECTED symbols remain eligible providers, while INTERNAL and
HIDDEN definitions cannot satisfy another image's undefined references.
`STB_GNU_UNIQUE` definitions now participate in DSO lookup alongside GLOBAL
and WEAK bindings, admitting the process-unique symbols emitted by C++
toolchains without weakening the visibility filter.
The DSO reader now validates the complete section-header table without
overflow-prone offset arithmetic, every consumed section range, linked string
table indices and types, and fixed-width `.dynsym`/`.dynamic` entry sizes.
Malformed shared objects therefore return a typed linker error before any
out-of-range byte read; mirrored x86_64 coverage corrupts a `.dynsym` string
table link to prove the fail-closed path.
Dynamic symbol names, version-definition names, and `DT_SONAME` now use a
checked string-table lookup. Out-of-range offsets and empty linkable symbol or
version names produce diagnostics instead of silently becoming empty strings
that could change provider selection or dependency identity.
