# Required HIR function entries

Authored manual for `test/01_unit/compiler/hir/hir_codec_required_functions_spec.spl`. Status: TEST_BLOCKED; seven scenarios authored, none executed. This document is not generated execution evidence.

| Scenario | Real setup and oracle |
|---|---|
| Legacy bodyful roundtrip | Parse/lower `answer() -> i64: 41`; encode and stable-decode; assert one named function, nonnil block/value, literal 41 and identical re-encoding |
| Canonical bounded roundtrip | Canonically encode the same real function; bounded decode; assert the actual body and identical canonical bytes |
| Explicit wire control | Build the real generated function payload into the documented module frame with both entry members present; legacy and bounded decode must preserve the body |
| Absent function value | Explicit key-present/value-absent frame must return nil from both legacy and stable decode |
| Absent function key | Explicit absent-key frame with a valid function payload must return nil from legacy and stable decode |
| Bounded refusal | Both malformed frames must return the exact malformed reason `missing_required_hir_module_function_entry` |
| Empty dictionary | A genuinely empty function dictionary must still encode and stable-decode with zero functions |

The malformed frame uses the authoritative schema: module name/path, empty imports/exports/domain blocks, absent symbol-table wire node, one function entry and sixteen empty trailing collections. Its all-present control prevents a malformed fixture shape from masquerading as a successful rejection test. Other nonnullable wire nodes may retain historical nullable behavior; this repair requires only function dictionary entries.

The production loader's existing decode-miss counter and writer's codec-refusal counter remain the admission owners. Malformed decoding skips dictionary insertion whenever the reader is invalid. A writer-runtime nil-assignment fixture was omitted because assigning nil to the declared nonoptional value type lacks established source acceptance; corrupted-state writer execution remains pending a supported fixture. The spec does not claim disk-cache integration, generator regeneration, compiler execution, or repair of the original value-loss mechanism. Required follow-up includes existing cache integration tests, real generator freshness and normal cache-enabled bootstrap admission.
