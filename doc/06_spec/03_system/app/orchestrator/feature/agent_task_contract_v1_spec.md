# Immutable task and use contracts V1

Status: **AUTHORED / NOT_RUN**. This manual was written alongside the executable
spec; it is not generated SPipe output or a passing verification receipt.

Source: `test/03_system/app/orchestrator/feature/agent_task_contract_v1_spec.spl`.
Requirements: REQ-TASK, REQ-TASK-USE from the approved TaskRef design/addendum.

The pure scenarios construct DATA only. They do not construct an authenticated
Controller owner, a signed retain/access approval, or execution authority.

| Scenario | Expected assertion |
| --- | --- |
| Preserve original task bytes | CRLF, CR, Unicode, literal `-`, and empty text round-trip unchanged; SHA256 covers the original bytes. CRLF and LF have distinct immutable identities. |
| Enforce bounds and integrity | 4096 raw UTF-8 bytes are allowed; 4097 ASCII bytes and 4098 Unicode bytes fail. Wrong digest, invalid namespace, control characters and padded references fail. |
| Decode strictly | Unknown/missing/mistyped fields, unsupported version, duplicate fields and noncanonical trailing data fail. |
| Pin invocation use | Controller/session/attempt determine stable use identity. Namespace, TaskRef, raw digest, source/catalog, model and Host scope affect the payload; another Controller/session/attempt changes identity. |
| Restrict initial adapter | Only Codex interactive Start with `codex-root-start-0.169.0-v1` is representable. Unsupported intent/provider/adapter, nonpositive attempt, invalid model, and malformed use records fail. |
| Scope retention | Controller, namespace, reference and raw digest distinguish retained task versions. There is no latest-version selector. |

`AgentTaskInputV1` remains the single task DTO. Stored task bytes contain no
normalization field. Provider-specific normalization belongs to a later invocation
adapter and must not overwrite the original digest. Model selection in a use
binding grants no permission to read or execute.

No runtime, compiler, native, branch-coverage or generated-manual check was run.
