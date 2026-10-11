# Flat pool truncation publication

Executable owner: `test/01_unit/compiler/frontend/flat_pool_truncation_spec.spl`.
Requirement: REQ-FLAT-POOL-TRUNCATION-001.

Decode truncated input with the actual compiler flat-pool owner. Allocating and
retained-destination variants must stop before appending a failed scalar or
incomplete child, and preserve `reader.ok=false`.

| Scenario pair | Input shape | Expected decoded prefix |
| --- | --- | --- |
| i64 / i64_into | two values declared, one available | empty |
| bool / bool_into | two values declared, one available | empty |
| text / text_into | two values declared, one available | empty |
| i64_list / i64_list_into | complete `[7]`, truncated next child | `[[7]]` |
| text_list / text_list_into | complete `[alpha]`, truncated next child | `[[alpha]]` |
| text_list_list / text_list_list_into | complete `[[alpha]]`, truncated next child | `[[[alpha]]]` |

Scalar length preflight rejects the whole scalar pool before reading its first
element. Nested length preflight checks child headers; a later failed child must
not erase complete earlier children or publish a partial child. A thirteenth
boundary scenario decodes `[[7], []]` and requires `reader.ok=true`.

Cached Stage 1 source-inline diagnostic: 13 executed, 13 passed, zero failed.
Release-source baseline: 13 executed, 7 passed, 6 failed. These results prove
the focused decoding mechanism only. Admitted self-hosted execution and native
qualification remain pending; no native result is inferred from the diagnostic.
Receipt/source hashes: `build/phase1-flat-pool-truncation-20261011`.
