# Windows private Engine exchange framing v3

Status: **SOURCE-ONLY NOT_RUN**. No compiler, test runner, Windows native call or
Docker request was executed. These authored cases are not qualification evidence.

Source: `src/lib/nogc_async_mut/container/providers/windows/docker_engine_exchange_v3.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/windows_docker_engine_exchange_v3_spec.spl`.

The private serializer accepts only exact API1.48 codec output. It rebuilds each
supported operation, compares the complete method/target/ordered headers/body,
and emits HTTP/1.1 with fixed Host docker and exact binary Content-Length.
Exec JSON uses the shared strict parser with bounded lexical depth/token checks;
rebuilding and byte equality reject unknown fields and alternate encodings.
No general HTTP client, shell, remote endpoint, version negotiation or retry is
introduced. JSON remains explicit Docker interoperability.

| Source case | Intended assertion |
| --- | --- |
| Fixed info wire | Exact request line, Host, zero length and connection-close bytes |
| All codec operations | Info, exact container/exec inspection, attach modes, exec create/start and both resize endpoints serialize; UTF8 body bytes survive unchanged |
| Framing mutations | Remote/CRLF targets, version/query/method changes, duplicate/injected/TE headers, unsupported operations and hijack mismatches fail |
| Exec mutations | Duplicate/unknown JSON fields, wrong user/privilege/TTY/output flags, wrong types, noncanonical bytes, malformed/oversize/non-UTF8 bodies and detached start fail |
| Resize and IDs | Noncanonical/extra/out-of-range query fields and truncated exact IDs fail |
| Context metadata | Create/start require matching action and raw64 domains; all other operations forbid context |
| Pre-acquisition rejection | Bad timeout limits or missing effect context reject before native connection |
| Read-only allowlist | Only canonical info and exact container-inspect requests pass the pure read-only wire gate |
| Data context cannot unlock mutations | Correct create/start bytes with matching, far-future context reject through both public acquisition entries |
| Other endpoints remain closed | Attach, both resize endpoints and exec inspection reject before native acquisition |
| Disguised mutation | Changing a mutation's operation label to info/container-inspect does not bypass full codec equality |
| Modified admitted request | POST method, nonempty body and hijack flags on the info target reject before native acquisition |
| Context on GET | The compatibility entry rejects write-context metadata even for an otherwise admitted GET |

The serializer and context checks are pure data functions. Even a positive
timestamp of1 passes context shape validation. They grant no IO capability.
Actual acquisition uses `begin_read_only_v3`, whose allowlist and exact canonical
request comparison run before clock sampling or native connection. The retained
`begin_v3` spelling enforces the same read-only restriction and forbids context.
Create/start, attach and resize remain unavailable through these public entries;
valid context, request framing or deadline cannot unlock them. The future effect
owner still requires real Host proof verification and a durable one-use claim
under the authoritative installed root. Those unfinished requirements are not
qualified by this read-only guard. Ready means read-only owner availability.

Fixed exchange bounds are header16KiB, request body64KiB, control body256KiB,
stream leftover1MiB and one native operation prefix at most64KiB. The transport
window is1..300000ms using actual monotonic time; it does not constrain workload
lifetime. Complete responses retain separate body and leftover bytes. Only an
actual parsed hijack can transfer the exact pipe lease and leftover together;
the present read-only acquisition profile cannot reach a hijacked session.
The receiving broker drains leftover before another read and separately admits
input/resize. HTTP completion, EOF, timeout or pipe cleanup proves no workload
termination, absence, rollback or capacity release.

The source holds exact cleanup ownership on failed connect/observe/write/read,
parse failure, timeout, cancellation and incomplete collection. poll performs at
most one bounded write OR one read after one native poll; no waiting loop,
reconnect or replay exists. A late response remains stored even when the window
check fails. Native collection clears a lease only after confirmed closure.

The class and lease values require sole broker-owner discipline. They are not
copy-safe multiple-reader capabilities. Transfer invalidates the authoritative
source value only; stale copied owners must never be invoked. The native owner
still enforces its admitted owner domain and generation checks.
