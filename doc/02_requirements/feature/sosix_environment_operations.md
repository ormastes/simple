# SOSIX environment operation tests

Scope: user-requested inspection and executable coverage of current hosted
SOSIX environment operations; no compiler rebuild or provider qualification
inferred from a diagnostic run.

| Requirement | Acceptance |
|---|---|
| REQ-SOSIX-ENV-ADMISSION | Reject empty, equals-containing, NUL and malformed UTF-8 keys/values before provider effects; expose codec errors where the runtime can carry malformed bytes. |
| REQ-SOSIX-ENV-LIFECYCLE | Preserve missing/empty getter contracts; assign, replace, remove and restore Unicode values; reject NUL replacement atomically; return checked cwd. |
| REQ-SOSIX-ENV-INHERITANCE | Matching-host child inherits current parent value; child changes do not mutate parent; removed value is absent in a newly launched child. |
| REQ-SOSIX-ENV-V4 | V4 explicit environment request codec preserves empty/Unicode values and canonical ordering, admits an explicit empty environment, rejects duplicates, unsorted keys, invalid names and NUL values. This is pure schema coverage. |
| REQ-SOSIX-ENV-WINDOWS | Windows key lookup ignores case, only tested on Windows. |

Nonmatching host scenarios and unsupported raw-byte carrier fixtures are
reported as reasoned planned cases, never counted as passes. Correct supported
behavior failures stay red. No environment snapshot/list API is exported by
`std.nogc_async_mut.sosix.environment`; no listing coverage is claimed.
