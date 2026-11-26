# aspect_pack host-offer setter rematerialized dictionary keys (2026-11-27)

Found by `test/01_unit/scripts/aspect_pack_cardinality_contract_test.shs` (unwired census,
`unwired_shs_tests_2026-11-26.md`).

`apk_loader_set_host_offer_v1` (`src/lib/common/aspect_pack.spl`) tested
`_ld_binding_index[ld].keys().len() > 0` to detect prior facet publication. That
materializes every key of the binding index on each call, the exact pattern the
cardinality contract removed elsewhere in the file (`_ld_binding_counts` is the O(1)
counter, kept in step at bind and unload). Fix: use `_ld_binding_counts[ld] > 0`.

Status: fixed, verification-pending (contract test green on Linux; the native/runtime lane
for aspect_pack specs was not re-run).
Repro: the contract test itself. Prevention: the same test now guards both key-count
forms (`_ld_binding_index[ld].keys().len()` and `_fc_unloaded.keys().len()`).
