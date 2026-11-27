# Build retention V1

Source: `test/01_unit/lib/scv/build_retention_v1_spec.spl`.

Audience: SCV and BuildRunner maintainers. This manually reviewed companion
describes authored executable checks; it is not generated execution evidence.

Execution status: **NOT_RUN**. No admitted general Simple test runtime was
available. No Rust seed or bootstrap-stage substitute was used.

| Requirement | Scenario and expected result |
|---|---|
| REQ-SCV-BUILD-RETENTION-001 | A sole authoritative receipt retains its historical snapshot closure. A zero budget evicts only an orphan and reports protected pressure. |
| REQ-SCV-BUILD-RETENTION-002 | `snapshot/same` and `artifact/same` are distinct. A branch pin protects only the exact named root and dependencies. |
| REQ-SCV-BUILD-RETENTION-003 | Missing edges, cycles and exhausted work budgets return errors before deletion authority exists. |
| REQ-SCV-BUILD-RETENTION-004 | An old client's reader lease retains its snapshot and base even after advisory expiry. Explicit release permits collection. |
| REQ-SCV-BUILD-RETENTION-005 | Repeating a pin or unpin at the current generation is idempotent; stale generation updates fail CAS. |
| REQ-SCV-BUILD-RETENTION-006 | A bounded deletion plan removes a rebuildable owner before its dependency. Non-rebuildable payloads stay protected even without the authoritative bit. |

Operational contract: pins support branch, selected release, worktree, draft,
active build, user, old-client and snapshot-dependent references. Namespace and
object identities use a bounded alphabet and cannot contain slash separators.
Complete graph validation includes unpinned objects. Storage pressure reports
`protected_over_budget` or `throttled`; it never authorizes loss of history.

These checks do not qualify physical filesystem eviction, runtime performance,
coverage percentage, or power-loss behavior. The integration companion covers
the checked snapshot-store route.
