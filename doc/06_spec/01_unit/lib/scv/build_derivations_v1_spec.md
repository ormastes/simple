# Complete outgoing derivation manifests

TDD source: `test/01_unit/lib/scv/build_derivations_v1_spec.spl`.

Status: authored before implementation; native runtime audit pending. This manual is hand maintained and is not generated execution evidence.

| Requirement | Observable contract |
|---|---|
| REQ-SCV-DER-001 | Replacing a consumer replaces its entire outgoing use set. |
| REQ-SCV-DER-002 | Reverse users and demand are derived exact sets; removing one consumer preserves another. |
| REQ-SCV-DER-003 | Root CAS, exact snapshot identity and registered attempt must match. |
| REQ-SCV-DER-004 | Identical operation replay is stable; changed payload under the same attempt ID is refused. |
| REQ-SCV-DER-005 | Duplicate uses and absent required scope roots are refused. |
| REQ-SCV-DER-006 | Pointcut universes retain negative candidates and empty scopes; change analysis sees old and new candidates. |
| REQ-SCV-DER-007 | Failed, cancelled or stale attempts cannot remove the previous manifest. |
| REQ-SCV-DER-008 | Persistence owner failure or wrong committed root prevents publication. |

Compiler owners supply the meaning of producer identities, facet digests and scope witnesses. These graph tests exercise deterministic indexing and transactional candidates, not compiler semantic completeness, a durable database, runtime qualification or artifact reuse authority. Positive persistence requires a real owner callback and integration evidence.
