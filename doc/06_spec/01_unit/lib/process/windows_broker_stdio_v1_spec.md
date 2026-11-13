# Windows broker stdio V1

Status: **NOT_RUN**. Authored pure assertions and source wiring checks; no
generated SPipe output or native Windows execution evidence is claimed.

| Requirement | Authored case | Expected result |
|---|---|---|
| REQ-WBS-001 | Native endpoint/file mode profile | Byte server synchronous stdin, byte client asynchronous merged stdout/stderr; synchronous stdout and mismatched endpoints refused |
| REQ-WBS-002 | Sole-reader byte count | Current maximum and available bytes both bound each ReadFile; invalid counts refused |
| REQ-WBS-003 | Managed profile admission | raw and broker-raw admitted with zero geometry; terminal geometry refused |
| REQ-WBS-004 | Parent pipe source wiring | broker-raw overlapped child output requests exact GENERIC_WRITE\|FILE_READ_ATTRIBUTES for GetNamedPipeInfo in existing HANDLE_LIST; raw anonymous pipe retained |
| REQ-WBS-005 | Pending query/write cleanup source wiring | SDK query storage, zero-time exact-handle completion wait followed by terminal IOSB, completion-before-free and lifetime no-reopen bound |
| REQ-WBS-006 | Private portable owner | Conditional Windows import, no public raw state, every native entry uses pinned thread |

The pure profile and count oracles are called by the native implementation.
Source assertions provide wiring evidence only, not failure injection evidence.

Required actual Windows fixture cases (all **NOT_RUN**):

1. Launch the pinned broker through broker-raw; verify native input sync and output
   async modes, same stdout/stderr and byte endpoints. Launch ordinary raw and
   require stdio open to reject its synchronous output before any WriteFile.
2. Force a mode query to remain pending. Open returns CleanupRequired with the
   same lease; cancel alone cannot free its query storage. WAIT_TIMEOUT and
   WAIT_FAILED must retain storage even if IOSB already changed. Only a signaled
   exact handle followed by terminal IOSB allows collection; a failed close/free
   remains retryable.
3. With the parent not reading, fill output until one write remains pending.
   Further writes return zero without replacing its buffer. Cancel then require
   actual completion before collection; unknown completion errors retain owner.
4. Fragment input and exercise zero/one/65536 available bytes with smaller call
   bounds. The only reader must return ordered bytes without blocking; a broken
   input pipe ends the stream and an unknown error does not fabricate EOF.
5. Exercise another-thread entry, attempted reopen after successful/failed open
   and after collection, and stdout/stderr alias cleanup under CloseHandle and
   HeapFree failures. No diagnostic print may contaminate the binary protocol.
