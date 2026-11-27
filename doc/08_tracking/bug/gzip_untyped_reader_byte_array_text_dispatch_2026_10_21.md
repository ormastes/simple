# Untyped gzip byte reader dispatch

Status: candidate implementation; TEST_BLOCKED (2026-11-03).

Commit b402f7d6e99 typed the gzip reader argument and extracted an explicit
`[u8]` match binding. This preserves production behavior but bypasses the
original untyped reader compiler defect.

The first faulty boundary is erased method dispatch after a tagged index
read. `lower_any_runtime_index_get` already uses the byte-aware `rt_index_get`
and marks its result as a runtime value. The erased text-builtin admission in
`method_calls_literals.spl` nevertheless routes `.to_i64()` to text parsing.
Returning the tagged word unchanged through `rt_to_int_dynamic` also gives
an incorrect integer. The candidate routes positively marked runtime values
with no competing collection/nominal/scalar owner to the existing
`rt_any_to_int` conversion. That runtime owner parses text and unboxes numeric
values. Raw scalar conversion retains its existing route. No C/runtime logic
was added and no gzip API annotation was removed.

The shared native fixture and qualification limitations are documented in
`gzip_optional_collection_payload_provenance_2026_10_21.md`. Exact byte values
139 and 255, a nil reader, erased text parsing, and raw integer conversion are
asserted. All behavioral checks remain UNRUN until an admitted producer exists.
