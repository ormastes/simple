# Selected Windows Container stream requirements

Selection: explicit full orchestrator/interactive scope, Windows Docker
process-only and all consumer effects through the Simple Container API.

| ID | Requirement | Required evidence |
|---|---|---|
| REQ-WDS-001 | Shared V3 tagged Windows policy and native owner; no app Docker calls or native fallback. | Actual common API consumer/source assertions. |
| REQ-WDS-002 | Exact retained container identity, scope, request and distinct helper operation. | Wrong-ID/scope/replay negatives. |
| REQ-WDS-003 | Native Job CPU/memory enforcement, readback and exact supported CPU quantum. | Pure arithmetic negatives plus real Windows observations, NOT_RUN. |
| REQ-WDS-004 | Launch deadline checked after preparation and before resume; separate lifetime timeout. | Expiry/no-entry and retained cleanup assertions. |
| REQ-WDS-005 | Single logical reader, bounded byte I/O, independent input/resize authority; detach closes only relay. | Backpressure, ownership transfer and authority negatives. |
| REQ-WDS-006 | Every uncertain native outcome retains cleanup owner until leader/Job/pipes are proved terminal. | Failure/cleanup source cases and Windows native test, NOT_RUN. |
| REQ-WDS-007 | Full interactive and exec require real container terminal/exec-instance observations. | Exact Engine exec ID, resize and ambiguous-start recovery evidence. |

Raw noninteractive support does not satisfy the final interactive criterion.
