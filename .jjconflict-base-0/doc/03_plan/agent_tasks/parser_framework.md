# Parser Framework Agent Tasks

## Frozen merge contract

Interfaces and step/checker names are frozen in `doc/05_design/parser_framework.md` and `.spipe/parser_framework/state.md`. Any change requires merge-owner review before dependent lanes continue. Temporary helpers fail with `assert(false)` or `fail(...)`; no placeholder pass is mergeable.

| Lane | Ownership | Depends on | Deliverable |
|---|---|---|---|
| A — identity/model | `src/lib/common/structural/identity.spl`, `parse/{contracts,model,output_plan}.spl` | none | snapshot, segmented arenas, scoped identities, result, pure output plans |
| B — dialect/scalar/sink | common `parse/dialect.spl`; default-tier `parse/{action_sink,scalar,runtime}.spl` | A | validated programs, indexed sink, scalar oracle |
| C — SIMD | default-tier `parse/structural_index.spl` | A-B | full continuation-state structural indexes and parity tests |
| D — GPU/parallel | default-tier `parse/parallel_lex.spl` plus existing GPU/MMU owners | A-C | total chunk tables, scan/count/emit, admission/private fallback |
| E — incremental/auto | default-tier `parse/{incremental,auto_profile}.spl` | A-C | lineage/stabilization/segment reuse/mappings/invalidation and measured selection |
| F — Simple adapter | `src/compiler/10.frontend/canonical_ast/`, `structural_adapter/` | A-B | one Simple program/schema plus legacy bridge |
| G — evidence/docs | parser specs, manual, benchmarks, guide | frozen APIs | independent parity/manual/NFR audit |

## Cooperative ownership

- Sidecars: lanes A-G may run independently only after interfaces are frozen; agents must not edit another lane's dirty files.
- Merge owner: root Codex.
- Final reviewer: root normal/highest-capability pass after independent evidence/manual audit.
- Manual steps: `Build the canonical parser representation`; `Parse the Simple dialect on the scalar CPU`; `Reuse SIMD structural indexes`; `Compose GPU lexical chunks in source order`; `Reparse only stabilized changed regions`; `Select the measured execution mode`; `Compare deterministic parser results`.
- Checkers: `parser_framework_fixture`, `parse_result_fingerprint`, `expect_parse_results_equal`, `expect_stage_receipts_deterministic`, `expect_tag_demand_allocation`, `expect_incremental_matches_full`.

## Merge order

`A -> B -> F -> C -> D/E -> G -> root verification`. C and F may proceed in parallel after A/B; D and E may proceed in parallel after scalar parity. The merge owner runs each unchanged acceptance command once and stops after three fix/verify cycles.
