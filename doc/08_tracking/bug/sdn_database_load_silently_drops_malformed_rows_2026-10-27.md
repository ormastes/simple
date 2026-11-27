# SDN database loading silently drops malformed rows (2026-10-27)

**Status:** OPEN — the loader is being changed to reject malformed table
sections. The historical canonical database remains unchanged and cannot be
registered through the ordinary writer until its malformed rows have an
owner-reviewed disposition.
**Severity:** P1 — loading and saving this database silently removes existing
records while producing a valid CRC.
**Component:** `src/lib/nogc_sync_mut/database/core.spl`

## Evidence

The pre-write canonical snapshot is retained at
`build/bugdb-writer-qualification/phase1refresh-20261027/canonical-registration-pre/bug_db.before.sdn`.
Its SHA-256 is
`278204ab0551e0e4cd016fc87f90c0321269d6858cd1ba59474fa551adee5093`.
The snapshot contains 182 `bugs_active` rows, 1,625 `bugs` rows, and 88
`bug_fix_strategies` rows. A sandbox load without logical edits reported 176,
1,612, and 87 rows respectively. The loader's row parser called `continue`
when a row's split field count differed from the table header, so those rows
were absent before serialization. A subsequent writer run had a valid CRC but
lost these unrelated rows. The canonical file was restored from the verified
snapshot and its SHA-256 and CRC were rechecked; no further canonical writes
are authorized.

The row-key and raw-line evidence is in
`build/bugdb-writer-qualification/phase1refresh-20261027/load-save-parsed-key-diff.json`.
The affected IDs are:

- `bugs_active` (6):
  `bootstrap_stage2_backend_object_path_status_2026_09_08`,
  `windows_bootstrap_cmp_authority_missing`,
  `stage3_hir_contract_model_partial_integration_2026_08_14`,
  `text-split-limit-ignored`,
  `compiled_checker_parser_category_c_2026_08_03`,
  `check_stage3_recovery_authority_arity_drift_2026_09_17`.
- `bugs` (13):
  `async_spec_promise_future_anon_tuple_state_inconsistency_2026-07-20`,
  `ci_workflow_path_filters_match_nothing_2026-07-28`,
  `dot_question_returns_optional_but_25_sites_return_it_as_bool_2026-08-09`,
  `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09`,
  `gated_specs_are_tautology_shells_2026-08-09`,
  `interp_env_get_name_collision_nil_root_2026-07-26`,
  `interp_lazy_import_global_first_use_unmaterialized_2026-07-15`,
  `interp_lint_main_then_frontend_dict_to_int_2026-07-28`,
  `interpreter_extern_registry_gap_blocks_os_specs_2026-08-04`,
  `match_enum_fallthrough_silent_2026-08-01`,
  `mutate_through_index_loses_write_2026-07-31`,
  `native_link_fabricates_weak_empty_extern_definitions_2026-08-01`,
  `spec_imports_declared_nowhere_2026-08-04`.
- `bug_fix_strategies` (1):
  `stage2_sanity_reverse_reference_publish_refused_2026_10_22`.

## Repair and verification plan for the 20 raw rows

No field boundary is inferred from a comma count. For each of the 19 bug rows,
the record owner must compare the exact retained raw line with its matching
bug document and any cited source/evidence, identify which existing field
contains the comma-bearing text, and approve a representation that preserves
the full original meaning. The repair should quote only a field whose boundary
is established by that evidence. If the evidence does not establish a unique
boundary, leave the raw line unchanged and keep the database blocked pending
the owner's decision.

The `stage2_sanity_reverse_reference_publish_refused_2026_10_22` line is in a
three-column strategy table but has the ten-field shape of a bug record. Its
owner must determine from its matching document and the strategy table's
contract whether this is a misplaced record or an intentional strategy entry;
do not move it or rewrite its fields until that disposition is explicit.

After each approved repair, verify the table header width, parsed row count,
all 20 record keys and full field values, and CRC on a disposable copy. Then
load/save the full snapshot in a sandbox and compare every preexisting table
and row semantically. Only after all rows round-trip without loss can a
separate canonical registration be considered. The canonical DB remains at
its verified pre-write bytes while this work is pending.

## Fail-closed source change

The candidate parser change returns failure on a row/header shape mismatch or
an unclosed quoted field. `SdnDatabase.load` rejects a malformed
table-shaped section instead of treating it as ignorable prose. A malformed
row-width unit case, valid quoted-comma unit case, and actual
`SdnDatabase.load` byte-preservation case passed on the pinned refreshed seed:
37/37 unit examples and 1/1 integration example. A temp-only app CLI run also
rejected both a malformed-row fixture and a copy of the retained historical
snapshot with exit 1 and the expected fail-closed diagnostic; each database
remained byte-identical. The copied historical snapshot's SHA-256 remained
`278204ab0551e0e4cd016fc87f90c0321269d6858cd1ba59474fa551adee5093`. The
canonical database remains at that same pre-write SHA-256. The watchdog receipt,
raw logs, report, harness and exact run are retained under
`build/bugdb-writer-qualification/phase1refresh-20261027/failclosed-attempt02/`.

These checks verify rejection without data loss; they do not repair the 20
historical rows, qualify a successful round trip of the full historical
snapshot, or authorize another canonical write. The existing bug-add writer's
six isolated temporary-project cases remain limited to its focused behaviors.
