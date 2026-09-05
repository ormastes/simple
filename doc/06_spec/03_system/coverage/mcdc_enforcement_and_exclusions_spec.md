# MC/DC Enforcement and Exclusions — Operator Manual

Executable: `test/03_system/coverage/mcdc_enforcement_and_exclusions_spec.spl`  
Status: **not executed in this lane**; hand-maintained mirror.

## Workflow

1. **validate reasoned exclusions** — demonstrate that only `covered == required` passes; 99/100 and 101/100 fail.
2. Admit a condition-scoped exclusion carrying stable identity, technical reason, reviewer, review ID, and expiry/version.
3. Reject blank reason, stale identity, and invalid broad scope with stable error codes.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-005 | Exact-completion boundary assertions |
| REQ-006 | Positive and three negative exclusion records |
| REQ-015 | Real assertions; no exclusion becomes covered or a generic passing skip |

