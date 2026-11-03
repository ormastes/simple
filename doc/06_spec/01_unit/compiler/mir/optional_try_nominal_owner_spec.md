# Optional Try nominal owner regression

Source: `test/01_unit/compiler/mir/optional_try_nominal_owner_spec.spl`.
Bug: `optional_try_nominal_owner_missing_2026_10_21`.

This is an authored manual, not generated execution evidence. Status:
**TEST_BLOCKED** until a qualified pure-Simple full CLI/test producer is available.

| Scenario | Actual boundary | Required observation | Result |
|---|---|---|---|
| Unannotated class payload | Real MIR `lower_try_expr` | Same symbol ID and provider-qualified class owner | UNRUN |
| Adjacent struct payload | Same lowering and shared decoder | Same symbol ID and existing struct provenance policy | UNRUN |

Native companion `database_optional_receiver_unannotated_probe.spl` uses actual
database owners and requires exact mutation, alias and persistence observations,
including missing-key/table branches. `native_optional_try_owner/main.spl` checks
an effectful imported getter, no repeated evaluation on either presence branch,
alias mutation and same-name local declaration isolation. These companion
executions are also UNRUN; source checks do not substitute for them.
