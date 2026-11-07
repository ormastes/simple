# Windows private Docker Engine pipe V1

Status: **NOT_RUN**. Manually authored companion for pure and source-contract
tests; no generated SPipe output or Windows execution evidence is claimed.

The broker owns generation-checked private IO slots for the fixed local
`\\.\pipe\docker_engine` endpoint. There is no process/job/credential registry
and no application-facing native HANDLE. The actual connected HANDLE remains
the authority; the observed server PID is never a container execution ID.

| Requirement | Scenario | Expected result |
|---|---|---|
| REQ-WEP-001 | Owner and DACL prerequisites | Exact SYSTEM/Builtin Administrators owner, protected present nonnull DACL |
| REQ-WEP-002 | Untrusted control and instance-creation grants | DELETE, WRITE_DAC, WRITE_OWNER, FILE_CREATE_PIPE_INSTANCE, GENERIC_WRITE and GENERIC_ALL refused, including mapped FILE_GENERIC_WRITE; unsupported ACEs refused |
| REQ-WEP-003 | Explicit admitted write context | Only create/start with raw64 lowercase digest, operation ID and positive absolute expiry; prefixed digest refused |
| REQ-WEP-004 | Completion classification | Incomplete/unknown remain owned; confirmed cancellation/end are distinct |
| REQ-WEP-005 | Native trust source wiring | Identification-only SQOS, actual security descriptor and server PID pre/post checks |
| REQ-WEP-006 | Byte writes and uncertainty | Separate ordinary/admitted methods, 64 KiB retained prefixes, no ambiguous replay |
| REQ-WEP-007 | Cleanup source wiring | Pending requests prevent free; failed LocalFree/CloseHandle/HeapFree stay owned |
| REQ-WEP-008 | Portable and thread ownership | Windows-only native imports; the same pinned owner-thread profile guards entries |
| REQ-WEP-009 | Generic exec birth digest compatibility | Actual ContainerExecRequestV3 digest admitted unchanged; changed argv changes digest |
| REQ-WEP-010 | Large completed read with smaller subsequent bounds | Native-used pure window oracle drains 65536 bytes as 3, 1 and 65532 bytes, preserving exact offsets; invalid bounds refused |

Each connection owns one read and one write OVERLAPPED, independent events and
64 KiB buffers. Limits are 64 active and 100000 nonreused lifetime IO slots.
Completed read remainders stay in owner storage until consumed; each Data respects
that call's maximum. Unknown immediate ReadFile failures retain pending ownership
and are not EOF evidence.
There is no implicit endpoint retry, arbitrary forwarding or process fallback.

The broker must validate HTTP payload identity and authorization. The generic
pipe owner does not mint a grant. Private create/start checks sample the actual
clock immediately before submission; they do not set running lifetime or undo
already transmitted bytes. Collect requests cancellation and may discard unread
bytes; closing a pipe never proves an Engine operation had no effect.

Native acceptance requires an isolated Windows fixture with a qualified Docker
endpoint, real trusted/untrusted/protected ACL cases, endpoint/PID changes,
simultaneous pending read/write, cancellation/completion races and failed native
releases, plus an actual large pending completion followed by smaller reads.
The generic exec fixture awaits the shared exec_v3 source integration. All cases,
compiler imports, ABI and performance remain NOT_RUN.
