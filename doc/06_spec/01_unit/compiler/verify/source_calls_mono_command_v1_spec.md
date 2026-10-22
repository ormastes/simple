# Source monomorphization: command inventory

Requirement: REQ-FV2-C1-SM. Executable specification:
`test/01_unit/compiler/verify/source_calls_mono_command_v1_spec.spl`.

Status: **6 scenarios authored; all UNRUN**. Manually maintained companion;
qualified SPipe execution, generated-manual verification, compilation and
coverage remain pending. No runtime or formal acceptance is claimed.

The intended public route is `simple gen-lean source-calls FILE.spl TARGET_TRIPLE`.
These scenarios invoke its actual `source_calls_command_v1` worker with an
exclusively created regular source file. They do not launch the app dispatcher or
a separate process. Fixture directories come from the canonical secure-temp
owner, and each owned directory is removed before assertions inspect results.

For successful commands, the report must exactly equal the direct source API's
inventory for the same source bytes, file path and target. The actual manifest
must close. The report uses `schema=SourceResolvedCalls-v2`, retains every prior
key and adds `mono_input_hir_hash`, `mono_output_hir_hash` and
`mono_specializations` matching actual returned metadata. Both HIR identities
must be nonempty. Status is `formal_status=NOT_CHECKED`; no PASS or v1 schema row.

| Scenario | Action | Required observation |
|---|---|---|
| Explicit generic call | Read identity<i64> from a real file with a space in its path | One binding and one specialization; exact command/direct report agreement |
| Default-only generic call | Read consume's omitted identity<i64> default | Two bindings and one specialization |
| Nongeneric compatibility | Read ordinary leaf and caller | One binding, zero specializations and all existing inventory fields under v2 |
| Target-selected requests | Read identical cfg source under x86_64 and aarch64 | One binding/specialization for x86_64, two for aarch64; explicit target retained |
| Malformed real file | Read invalid generic syntax | Parser error with no partial inventory or unchecked-status row |
| Implicit target | Pass native with a valid regular file | Target error with no inventory |

The helper does not simulate write/read failures with directory paths. External
CLI dispatch, native execution, authenticated checking and release remain separate
qualification obligations.
