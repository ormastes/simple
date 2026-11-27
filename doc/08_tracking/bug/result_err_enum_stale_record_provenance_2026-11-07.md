# Declared Result Err enum inherits an unrelated record owner

Status: source repair and regression specifications authored; runtime verification pending.

The single-payload arm in `switch_operators_calls.spl` decodes a declared enum
Err payload and remembers its correct HIR type, then can assign
`enum_payload_struct_names["Result::Err"]` to its `struct_value_syms` entry.
The shared slot can name a record from another Result instantiation. Named
enum types were excluded from neither that fallback nor its structural-type
veto, while exact record-owner recovery deliberately recognizes Class/Struct.

`resolve_base_struct_name` consults this value-owner entry before HIR, so the
enum can acquire a false record owner despite retaining its enum declaration.
The same fallback can stamp the legacy text marker as a record owner.

The repair vetoes this fallback only when the subject's recovered payload
type names a resolved Enum symbol. Existing exact Class/Struct recovery and
erased Any fallback remain intact. This does not add type-alias resolution.

`test/01_unit/compiler/50.mir/result_enum_payload_record_provenance_spec.spl`
parses and lowers a real Result match, changes only the shared fallback slot,
then lowers the parsed function again. Assertions inspect the binder's HIR
type, runtime enum marker, record-owner entry, and downstream record-owner
lookup. Controls cover a foreign record, the text marker, exact Struct/Class
payloads, and erased Any fallback.

`test/fixtures/compiler/native_result_err_generic_method_payload.spl` adds a
distinct Err-record producer and payload-value check before the generic-method
enum replay. Native compilation/execution remains pending.

This is an independent source-proven provenance defect. It does **not**
establish the cause of the historical generic-method `<invalid-heap>` failure
in `simple_ring_result_payload_provenance_2026-11-06.md`; that failure remains
open. Current ordinary enum extraction already records its payload HIR type,
so no duplicate remember-type write was added.

No Simple test or native fixture was executed for this repair; no Rust seed
fallback was used. Source review and authored tests are not runtime PASS
evidence. Resume with the focused spec, native replay in both supported
backends, and required compiler/core and MCP/LSP smoke checks through an
admitted self-hosted runtime.
