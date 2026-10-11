# Native SCV digest validation rejects a 64-byte digest

Status: OPEN compiler/runtime boundary defect.

In the 66-module no-stub Stage 2 tracked-move executable, the first cold
event reaches `compile_source_inventory_entry_valid_unscoped_v1` with a
positive 24-byte count. GDB shows the first digest text has length 64, but
`compile_source_inventory_digest_valid_v1` returns false. That validator
converts text through `text_to_utf8_bytes` before checking the returned
array length and lowercase hex bytes. The runtime emits `rejected invalid
array handle before dereference` on this path. The exact call that emits
the warning has not yet been isolated.

The source candidate uses `value.bytes()` for the validator's same UTF-8
byte stream. It is unbuilt after this turn's three-build limit. Run the
focused event probe and full V4 tracked-move fixture in the next bounded
cycle; require valid digest bytes, cold and warm admissions, and no native
invalid-handle warning before closing this bug.
