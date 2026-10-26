# Compiler consumers omit six split helper imports

Status: import-only repairs applied locally; executable tests and performance
qualification pending. No Phase3 PASS or remote landing.

The test-runner construction from committed source `abb0891dcc048958ea2030759802ad7ae0cedc76`
plus two separately reviewed facade repairs produced 580 HIR cache records and
26 failed entries. A bounded direct object diagnostic for
`hir_lowering/_Items/declaration_lowering.spl` retained seven fatal diagnostic
sites naming six helpers across four consumers. It exited 1 in HIR after
67.168 seconds, with sampled process-tree peak RSS 746,680 KiB. This does not
attribute the other failed entries to these imports.

| Consumer | Missing name | Existing owner |
|---|---|---|
| `hir_lowering/_Items/declaration_lowering.spl` | `function_params`, `platform_attr_fields_for`, `bootstrap_hir_symbol_for_name` | sibling `_Items/lowering_helpers.spl` |
| `core/parser_stmts.spl` | `expr_mark_colon_block` | `core/_AstExpr/nodes.spl`, already exported by `core/ast_expr.spl` |
| `hir_lowering/module_surface_registry.spl` | `module_surfaces_validate_index_alignment` (two sites) | `module_surface_registry_index.spl` |
| `hir_lowering/module_surface_export_index.spl` | `module_surface_export_origin_index_position` | `module_surface_types.spl` |

All definitions are already present in the captured closure. The first consumer
imported only `PlatformAttrFields` from its helper owner. The registry consumers
likewise omitted the called helper from existing named import lists. The repair
adds explicit canonical imports only; function bodies, validation, visibility,
generics, runtime and cache identity rules are unchanged. The parser uses the
existing AST expression facade instead of exposing a new private implementation.

Evidence is retained under
`build/native_probe/build-runner-review-20261011/`:

* `test-failed-direct-01-declaration_lowering/child.log` and `result.json` retain
  actual failure diagnostics and authenticated bounded-process receipt.
* `TEST_RUNNER_TERMINAL_LEDGER.json` records the separate 580/26 outcomes.
* `test-import-repair-proposal/source.patch` is the reviewed four-file import
  delta; `PROPOSAL.json` pins the original and candidate bytes.

Regression coverage authored at
`test/01_unit/compiler/hir/compiler_helper_import_bindings_spec.spl` executes
real consumers: trailing-colon lambda marking, typed function parameters,
explicit bootstrap-flat function lowering with its canonical main symbol,
successful registry publication, malformed index rejection, wildcard facade
origin resolution with owner/source assertions bound to the matching name row,
and platform attribute warning projection through struct
lowering. These seven scenarios are **UNRUN**; API/arity source review is not an
execution PASS. Existing native-safe module-surface index/owner specs remain
required, as do affected compiler/core checks under a qualified pure runtime.

The import-only edit performs no additional algorithmic work in consumer bodies,
but that is not a measured no-regression result. Matched completed-work
throughput and peak RSS are still required before admission. The failed
diagnostic's runtime/RSS cannot serve as a successful workload baseline.

The active 26-entry diagnostic source/cache stays frozen. No aggregate rebuild
or extra retry was performed while applying this local repair. Authoritative
bug DB reconciliation remains pending a qualified pure CLI.

## Follow-up: SSA definition counter import

The closed direct diagnostic for `var_reassign_ssa.spl` (task20 of the
fourteen-entry continuation) exited 1 after 54.231 seconds, with sampled
process-tree peak RSS 662168 KiB. It identified both `var_reassign_local_id_value`
and `local_count_increment` as missing. The first reviewed follow-up import
covered only the former, so it did not fully repair this entry.

The remaining call is in the actual `ssa_reassigned_locals_for_blocks` consumer.
Its existing owner `var_reassign_analysis.spl` defines
`local_count_increment(local_ids: [i64], counts: [i64], local_id: i64)` returning
the updated pair of arrays. The caller needs this helper for both the first
definition and later definitions of a local. Root applied one additional named
import, preserving the existing counting implementation and earlier import.
The reviewed source hashes are `63db6755b63a6f87591cedce02f9352ba77fc35b2e9ae6be0e9255e6c8596298`
before and `942db9cf827116e41bfeab091193f762620069caea3ed3cc881da61275b9dd60`
after. Evidence and the exact proposal are under
`build/native_probe/build-runner-review-20261011/ssa-count-import-proposal/`.

The two real consumer cases in
`test/01_unit/compiler/hir/ssa_reassignment_count_binding_spec.spl` verify
repeated definitions of LocalId 0 across blocks, repeated nonzero definitions
reported once, and exclusion of single-write locals. Both cases are **UNRUN**.
No source-text assertion or successful import is a behavioral PASS.

The original 26 diagnostics are closed. The separately frozen final-six packet
contains only its previously reviewed seven imports and deliberately excludes
task 20 and this later repair. No live input was changed. The helper's original
array-update behavior is unchanged, but matched successful-work throughput and
RSS remain unmeasured; this report grants no performance or Phase3 admission.
