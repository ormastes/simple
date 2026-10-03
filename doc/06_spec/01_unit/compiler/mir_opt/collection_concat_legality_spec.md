# Array concat legality preservation

Authored manual, 2026-10-03. Source:
`test/01_unit/compiler/mir_opt/collection_concat_legality_spec.spl`.
Five scenarios are unexecuted; this is partial REQ-008 regression coverage.

| Scenario | Production assertion |
|---|---|
| Different copy destination | Complete blocks, including the returned destination, remain identical. |
| Live temporary definitions | The aggregate and concat result remain defined for a later observing call. |
| Unproven operator ownership | A `+` spelling does not authorize replacement by mutation. |
| Observable alias | A prior copy of the left operand and subsequent observation remain intact. |
| Direct matcher | Without an authority-bearing API, the helper returns no replacement. |

The first four cases run `collection_opt_run_on_function` on constructed MIR
and compare the entire block sequence, including terminators, with the input;
they also require `concat_replaced == 0`. They do not execute compiled programs
or prove actual alias/runtime behavior. The helper case prevents bypassing the
same legality boundary through direct callers.

The repair intentionally retains allocation and copying costs of array concat
until ownership, liveness and mutation legality are established. String concat
and other optimizer transformations have separate contracts and are unchanged.
