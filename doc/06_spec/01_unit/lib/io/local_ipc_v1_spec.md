# Owned local Unix connection

Simple spec: `test/01_unit/lib/io/local_ipc_v1_spec.spl` — three groups,
**NOT_RUN**. Native fixture: `src/runtime/test/local_unix_v1_selfcheck.c` —
**PASS**, one CoreC build and run on 2026-11-07, both exit 0.
Exact commands, compiler/binary hashes and unchanged before/after hashes for 15
source inputs are in `local_ipc_v1_native_evidence.sdn`; captured output is in
`local_ipc_v1_native_stdout.txt`. This inventory is the explicit translation
units and included owner boundary, not a full system dependency closure.
That PASS predates the fork-origin correction and remains historical; it does
not qualify the subsequently changed native header.

The Simple cases check lexical rejection before connect, owner retention on
invalid IO/close/admission input, and stale-token versus EOF behavior. Platforms
without the native implementation must report unsupported explicitly.

The native fixture uses real Linux sockets and the actual canonical registry.
It links normal CoreC array/memory/process support; there are no alternate array
or registry stubs. Its raw listeners and descriptor inspection are test-only.

| Requirement | Actual fixture mechanism |
|---|---|
| Kernel peer and anchored path | Real connect plus SO_PEERCRED, nofollow parent rejection, embedded NUL and wrong UID rejection. |
| Partial progress and bounds | Small socket send buffer, partial write, saturated buffer timeout, exact received bytes and EOF. |
| Submission admission | Already expired send submits zero bytes; delayed peer drain wakes a saturated send after expiry, which still submits zero. |
| Descriptor hygiene | CLOEXEC/NONBLOCK checks; one and 32 SCM_RIGHTS descriptors rejected and all received copies disposed, including truncation. |
| Exclusive operation | Busy close/write preserve the connection without blocking on its operation lock. |
| Stale copies | Closed generation cannot read/write/close a successor in the same slot or close a reused raw descriptor. |
| Capacity and wrap | 64 live slots reject the next installation; owner close returns descriptor count to baseline; generation exhaustion rejects reuse. |

The fixture's positive peer is the same test UID. This proves the configured
trusted-UID connection contract, not distinct-UID isolation. The strict Host
gateway, listener/frame/SCM_RIGHTS export/adoption, Simple compiled facade,
Windows behavior and full application acceptance remain separate gates.

The reviewed private recipe used `taskset -c 0-4`, a 120-second build deadline,
one 15-second run and a private TMPDIR. Build took 2.206 seconds and run took
0.202 seconds; peak allocated artifact storage was 2,588,672 bytes against a
128 MiB cap. Preserve the evidence; do not repeat this passing run unchanged.

The separate `src/runtime/test/local_unix_fork_origin_v1_selfcheck.c` is authored
for the subsequent fork-safety correction and is **NOT_RUN**. It holds both parent
registry and operation locks plus the actual runtime immortal-registry spinlock
across fork, requires all five inherited-owner calls to return NULL without
allocation, consuming bytes, connecting, writing or closing, then exercises
the parent's retained connection. It also covers independent first use in a
child forked before any owner existed. This is a new failure scenario, not a
repeat of the historical passing IO fixture.
In the independently initialized child it also injects one actual namespace
observation failure with a `--wrap=stat` wrapper that delegates every other call
to the real provider. Restored observation must leave the owner quarantined;
all five future calls refuse before stat or socket effects. Privileged namespace
changes and PID-collision execution remain NOT_RUN.
