# Replan — Remaining Architecture Batches

**Date:** 2026-04-27 (after 11 commits shipped, sync clean)

## What's done (cumulative across sessions)

| Layer | Files refactored | Groups eliminated | Helper(s) introduced |
|---|---|---|---|
| 35.semantics/lint | 8 lint files | 10 (21→11) | `lint_text.iter_code_lines` + `count_triple_quotes` |
| 70.backend/native | x86_64_simd | 1 (within-file) | `_encode_simd_3op_ymm` |
| 70.backend/native | native_elf, native_macho | ~3-4 (cross-file) | `collect_section_bytes` |
| 80.driver/shb | shb_reader | 1 (within-file) | `_open_section + _SectionCursor` |
| 80.driver | driver_public_{api,compile,shared} | ~11 (cross-file) | `find_simple_binary`, `clean_child_output` |
| 40.mono | monomorphize/deferred_deserialize | 4 (within-file) | `_read_def_prefix`, `_read_def_suffix` |

**Total commits:** 11 (nptolssx → vxyxnxop). All on `origin/main`. Bootstrap verified clean for commit 1; commits 7-11 are lint-clean but not bootstrap-verified.

## What remains — REVISED batch plan

(Numbers will be refreshed against post-refactor dup-check below)

### Tier 1 — Within-file Pattern C (lowest risk, ship fast)

| # | Target | Layer | Original groups | Notes |
|---|---|---|---:|---|
| R1 | `90.tools/fix/main.spl` | 90.tools | 2 (impact 325) | Within-file Pattern C — read & confirm pattern is mechanical |
| R2 | `90.tools/header_gen/c_header.spl` | 90.tools | 4 (impact 305) | Within-file |
| R3 | `90.tools/verify/compare_features.spl` | 90.tools | 2 (impact 208) | Within-file |
| R4 | `10.frontend/core/lexer.spl` | 10.frontend | 3 (impact 230) | Within-file (verify — may be cross-file with other lexer fragments) |
| R5 | `10.frontend/core/alloc_inference.spl` | 10.frontend | 2 (impact 134) | Within-file |
| R6 | `50.mir + 60.mir_opt + 99.loader long-tail` | mixed | 5 total | Long-tail cleanup; 2-4 files; small impact |

### Tier 2 — Within-file but trickier (defer to mid-cycle)

| # | Target | Layer | Original groups | Risk |
|---|---|---|---:|---|
| R7 | `vhdl_backend.spl` | 70.backend | 4 | Deep nested match arms in 2,893-line file. Result-propagate `?` opportunity. |
| R8 | `type_layout.spl` | 30.types | 3 | Nullable `has_i64` returns from match — verify Simple `?` syntax in match position first |
| R9 | `40.mono/monomorphize/deferred_deserialize.spl` REMAINING | 40.mono | 2 | After my refactor, 2 groups remain (variant-specific reads). May fold into Tier 1. |

### Tier 3 — Cross-file Pattern A/B/D (highest design cost, ship last)

| # | Target | Layer | Original groups | Pattern |
|---|---|---|---:|---|
| R10 | `90.tools/ffi_gen/type_mapping.spl` ↔ `70.backend/.../type_mapper.spl` | cross-layer | 8 | **Pattern D** — but this is a layer-direction question; may be intentional duplication. Investigate first. |
| R11 | `cranelift_type_mapper` + `cuda_type_mapper` + `interpreter_type_mapper` + `llvm_type_mapper` + `vulkan_type_mapper` + `wasm_type_mapper` + `common/type_mapper` | 70.backend | 6+ shared | **Pattern B** sibling-file branch ladders. Needs trait-or-free-function design (Simple has no inheritance + closure-modify limits). |
| R12 | `isel_aarch64` + `isel_riscv32` + `isel_riscv64` + `isel_x86_64` cluster | 70.backend | 10+ | **Pattern A** sibling boilerplate. Extract `prepare_isel_module` + `finalize_isel_module`. |
| R13 | `70.backend/linker/linker_wrapper.spl` cluster | 70.backend | 4 cross-file with linker_wrapper_lib_support / obj_taker | Pattern D (linker-side cross-file) |
| R14 | `10.frontend/treesitter/outline_decls.spl` + `interpreter/cli_eval.spl` + `core/ast.spl` (cosine-only) | 10.frontend | 5 | Mixed within/cross — needs per-file pattern analysis |
| R15 | `80.driver/build/main.spl` | 80.driver | 2 | After driver_public_* cleanup — may already be lower since some shared boilerplate is gone |
| R16 | `40.mono/monomorphize/deferred.spl` | 40.mono | 4 | Sister file to deferred_deserialize.spl; may benefit from same prefix/suffix helpers |

### Tier 4 — Coupling & cohesion (separate from duplication)

| # | Target | Action |
|---|---|---|
| R17 | High-fan-out files (≥10 imports, non-parser): `30.types/{associated_types,variance,higher_rank_poly}.spl`, `99.loader/loader/module_loader.spl`, `10.frontend/core/ast_clone.spl` | Spot-check for import-facade refactor; ship only if a clear win is visible (per advisor sequencing) |
| R18 | Build proper coupling tooling (CBO/RFC/LCOM/SCC) | Filed as separate enhancement request — out of scope for this cycle |

## Sequencing recommendation

**Session N+1 (next):**
1. R1 — `90.tools/fix/main.spl` (clean within-file)
2. R2 — `90.tools/header_gen/c_header.spl`
3. R3 — `90.tools/verify/compare_features.spl`
4. Bootstrap verification after commits 12-14 (covers commits 7-14 cumulatively, closing the verification gap)

**Session N+2:**
5. R4 — `10.frontend/core/lexer.spl`
6. R5 — `10.frontend/core/alloc_inference.spl`
7. R6 — long-tail (50.mir, 60.mir_opt, 99.loader)
8. R7 — `vhdl_backend.spl` (after re-reading existing `?` operator usage in similar files)

**Session N+3+:**
- Tier 3 (cross-file) batches in order of clarity
- Tier 4 (coupling) only if clear wins visible

## Anti-pattern to avoid

- Trying to do Tier 2/3 batches without first confirming Simple language syntax assumptions (especially nullable types, generics, traits).
- Spawning >2 parallel agents per session — coordination cost (jj race, lock contention) outweighs parallelism benefit.
- Bundling sub-batches into one commit window — commit IMMEDIATELY after lint-clean per `feedback_jj_uncommitted_clobbered_by_parallel.md`.

## Bootstrap gate status

Last full bootstrap: after commit `nptolssx` (batch 1). Commits 7-11 (toyzskou, xtvppnkn, oloutpqt, oplvpuqm, vxyxnxop) NOT bootstrap-verified individually. Recommendation: run one cumulative bootstrap before starting R1.

## Numbers (filled when current dup-check completes)

| Layer | Original | Now | Change |
|---|---:|---:|---:|
| 35.semantics | 21 / 691 | 11 / 306 | -10 / -385 |
| 70.backend | 38 / 919 | _scan in flight (multi-min)_ | _expected ~32-35 / ~750_ |
| 80.driver | 17 / 375 | _scan in flight_ | _expected ~5 / ~120 (driver_public_* + shb_reader cleaned)_ |
| 40.mono | 7 / 163 | **3 / 63** | **-4 / -100 (-61%)** |
| 90.tools | 18 / 491 | (untouched, expected ~18) | 0 |
| 10.frontend | 15 / 308 | (untouched) | 0 |
| 30.types | 6 / 146 | (untouched) | 0 |
| 50.mir | 2 / 48 | (untouched) | 0 |
| 60.mir_opt | 2 / 48 | (untouched) | 0 |
| 99.loader | 1 / 24 | (untouched) | 0 |

Estimated cumulative reduction: ~30-35 of 127 line-mode groups (~25-28%). Remaining work = ~92-97 groups across the tiers above.
