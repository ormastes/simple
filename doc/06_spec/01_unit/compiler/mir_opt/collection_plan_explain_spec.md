# Collection plan explanation: authored acceptance companion

Source: `test/01_unit/compiler/mir_opt/collection_plan_explain_spec.spl`.
This is an authored companion, not a generated or executed report.

| Scenario | Assertion contract |
|---|---|
| Admitted workload | Report the returned Hash decision, profile facts, size rejection, selected extra bytes and exact budget. |
| Failed correctness gate | Report Original, the P0 blocker and absent profile evidence. |
| Fitting alternative | Hash bound 64 exceeds budget 48; Ordered bound 48 fits; explain both bounds and the hash rejection. |
| Unknown versus zero | Unknown hash estimate stays `unknown`; a supplied zero linear estimate stays numeric zero. |
| Original without a budget | Explain unknown budget and Original fallback; extra bytes zero describes added optimizer memory only. |
| Invalid bounds | A value below -1 is `invalid`, not unknown or zero, and selection rejects it. |

Tests call the actual selector and renderer. Memory fields are upper-bound
facts supplied by the proof owner for the supported population, not profile
p95-derived estimates, observed RSS or evidence that selected MIR ran.

Test-first commit: `db0b7694c29`; renderer implementation: `0428efd8edb`.
Independent review corrected the admitted-workload fixture to supply a linear
memory bound, preserving its size-rejection oracle after memory admission was
introduced. Runtime verification and admitted doc generation remain pending.
