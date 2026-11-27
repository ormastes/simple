# Schema-aware textual database row proposals

**Manually authored BDD manual. Execution: NOT_RUN.** This is not SPipe docgen,
test-pass, coverage, runtime admission or settlement evidence. The executable
spec is `test/02_integration/lib/scv/solver_db_rows_schema_v1_spec.spl`.

The submitted snapshot and signed V1 patch use the original schema. The host
separately pins the current schema and accepted policy. This bounded adapter
supports one table and scalar field updates. A draft always retains exact input
text, and independent validation remains required.

| Scenario | Given / When | Expected observable result |
|---|---|---|
| Rename and offline update | The host renames `title` to `summary`; a signed old-schema update changes its value. | The actual reducer previews the update, the projected row uses `summary`, and the original ColumnUid, signed patch text and snapshot remain intact. |
| Independent column additions | Two schema branches add distinct nullable/defaulted columns before importing an old row update. | Both column identities remain; the old row gains no padded cells or eager defaults. |
| Changed submitted bytes | Submitted patch bytes differ from the host's frozen input hash. | Binding fails with no preview; every submitted byte remains available. |
| Combined uniqueness | Updating one row would duplicate another row's unique title. | The existing reducer reports the transaction-wide collision and retains the original snapshot without a candidate root. |
| Concurrent scalar edits | The current original-schema snapshot contains a third value. | The reducer retains an explicit concurrent-field conflict and its alternative-value record. |
| Changed default | An existing column's default changes while an old-schema edit arrives. | A reviewed definition migration is required; no preview is produced. |
| Strict malformed-input reader | The host freezes the exact hash of a malformed V1 patch. | The existing strict reader rejects the text; its full bytes remain intact. |
| Changed type or merge policy | The host supplies a different frozen current definition. | An explicit type/policy migration is required before interpreting the old write. |
| Changed catalog pin | A valid replacement schema differs from the accepted mapping identity. | The mapping binding fails before reduction. |
| Missing historical binding | The historical V1 binding digest is absent or invalid. | The result requests inputs and never guesses a column mapping. |
| Drop and update | The current schema tombstones the column being edited. | The drop/update conflict remains explicit with no preview. |
| Wrong provider domain | A source-byte solver is supplied for the DB request. | Host preflight reports unsupported; DB input is not text-merged. |
| Resource bounds and cancellation | Input bytes exceed the budget, or the request is cancelled. | Reading/reduction stops with its typed refusal and retains the exact submitted text. |

Every computed draft remains `needs_inputs` with unqualified builtin execution,
an empty deterministic result key and external validation required. The required
checks bind the combined current schema and projected snapshot candidate.

Runtime command, once an admitted general pure-Simple runtime is available:
`<runtime> test test/02_integration/lib/scv/solver_db_rows_schema_v1_spec.spl --mode=interpreter`.
No runtime, SPipe generation, manual-maintenance score, native smoke or
performance measurement was executed for this authored manual.
