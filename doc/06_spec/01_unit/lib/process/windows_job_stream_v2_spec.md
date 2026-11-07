# Windows managed RAW Job stream V2

Status: **NOT_RUN**. This manually authored companion describes the executable
unit/source contract. It is not generated SPipe output or Windows qualification.

The native owner uses the existing Windows PTY registry in RAW mode. It creates
no pseudoconsole and merges stdout and stderr into one byte stream. Public
container input remains disabled until the caller provides separate authority.

| Requirement | Executable scenario | Expected result |
|---|---|---|
| REQ-WJS-001 | Derive CPU quantum; reject nesting and multiple groups | N/gcd(N,10), single group, 1–64 processors |
| REQ-WJS-002 | Convert CPU requests exactly | No rounding; rate is cpuMillis×10/N in 1–10000 |
| REQ-WJS-003 | Validate RAW launch and pinned executable | Absolute paths, raw SHA256 producer identity, rows/cols zero |
| REQ-WJS-004 | Validate exact environment and budgets | Case aliases, malformed assignments, zero memory/expiry rejected |
| REQ-WJS-005 | Review source ownership and cleanup gates | Same nonreused slot, generation checked, unknown child retained |
| REQ-WJS-006 | Review native launch and Job policy | Memory/CPU readbacks; topology/nesting/clock checks before create/resume |
| REQ-WJS-007 | Review byte transport and backpressure | Raw bytes, 8192-byte reads, 4096-byte pending writes, resize refused |
| REQ-WJS-008 | Review portable wrapper | Windows-only native import; explicit unsupported fallback |
| REQ-WJS-009 | Review retained CNG/heap failure ledger | Hash, algorithm, and failed buffers remain in the same cleanup lease; hash release precedes algorithm/buffer release |

The managed producer-pin path also retains a failed UTF-16 path release. Its
hash scan is capped at 256 MiB and samples the actual launch clock before and
after each bounded file read. A native file read can still incur OS I/O delay;
no hard bound on kernel scheduling or disk completion is claimed.

Native acceptance still requires an admitted Windows binary and real negative
tests for failed CreateProcess, Job assignment, readback, expiry while suspended,
partial/pending writes, descendant cleanup, and failed CloseHandle/HeapFree.
Source assertions verify wiring only. No CPU enforcement, cleanup completeness,
Windows execution, compiler admission, or coverage percentage is claimed here.
