# Distributed executable verifier: byte-exact OCI output evidence

Status: open. A pinned V4 invocation-byte observer and fail-closed Simple
verifier parent/worker are drafted; a production `simple-dist-exec-result-v1`
receipt remains blocked.

## Current boundary

`two_node_staged_qualification.spl` accepts a receipt from an independently
pinned verifier. The new verifier entrypoint rejects before OCI launch because
its parent bridge is unqualified. The image-resident worker rejects the current
leader-only V4 runtime before process pin/start. The Linux OCI
provider's `logs()` returns bounded `text` without a retained-byte count or
truncation/completeness proof. Hashing that text cannot prove the exact stdout
bytes of a program that may emit non-UTF-8 data or exceed the 1 MiB cap.
`oci_exact_logs_v1.spl` now has a separate V4 pinned-engine observation of one
`logs` invocation, with raw bytes, EOF/count checks and retryable ownership.
It is unrun and does not bind the observed container to the provider's earlier
create/start/wait identity or prove that the engine itself supplied complete
container stdout.
The provider also resolves `podman`/`docker` by name, while the staged
qualification pins the verifier binary but not its native engine executable.
The deployed V4 runtime currently rejects non-`Leader` descendant policy in
`src/runtime/runtime_process_owned.c` near line 3691 and sets `tree_empty=0`
near line 3248. Its frozen receipt invariant requires `tree_empty=true`, so a
worker cannot claim a complete frozen child observation on this runtime.
The artifact child also inherits the worker's access to a writable output
mount unless the image supplies a separate result-writer authority; a child
could forge the committed result before OCI destruction.
On the current macOS Docker Desktop host, an unprivileged Debian bookworm
container reports `cgroup2fs`, but `/sys/fs/cgroup` is not writable (`test -w`
returned exit 1). This is a diagnostic for this host, not a qualification of
all Linux workers; no delegated cgroup is available to the worker here.
The native V4 fix must own a fresh delegated cgroup leaf per ticket, attach
the child before workload execution, keep control after the leader exits,
observe `cgroup.events populated=0` after reap, and retain cleanup authority
through failed exec, timeouts and publication errors. Merely changing the
request admission bit would create false frozen receipts. Memory-controller
enforcement must be reported separately from `RLIMIT_AS`.

## Required fix

1. Pin the exact OCI engine executable and controlled process environment used
   for probe, create, start, wait, inspect and destroy. Preserve the provider's
   identity, attempt, boot and generation checks.
2. Implement a Simple verifier that accepts only two pinned artifact arguments
   and snapshots the exact exported bytes into a trusted private input mount.
   Run a pinned Simple verifier worker **inside** the OCI image with network
   disabled. Add an actual descendant containment capability with an honest
   `tree_empty` proof, plus a worker-only result-writer boundary inaccessible
   to the artifact child. The worker must capture its child executable through
   the owned V4 byte stream, then durably write exact stdout bytes and a
   canonical measured result into a private output mount. Engine `logs` are diagnostics only:
   successful CLI byte capture cannot establish backend log completeness.
3. The parent must verify the mounted result's exact bytes, digest, exit and
   worker/image/attempt binding after terminal wait; destroy the container and
   observe cleanup before emitting the staged controller receipt. Missing or
   uncertain result or cleanup never produces a success receipt.
4. Qualify the verifier image, host mount ownership, engine pin, negative
   lifecycle cases and exact stdout bytes on a live Linux worker. The staged
   controller must bind that qualified verifier identity to its fixture.

## Required cases

Empty stdout, embedded NUL, invalid UTF-8, output at/over the cap, truncated
capture, nonzero program exit, start/wait/logs/destroy failure, wrong artifact
digest, modified artifact after snapshot, stale provider generation, changed
engine binary, and a normal live execution with exact receipt bytes.

No current source-only test or receipt parser closes this live evidence gap.

The parent now has a separate source-draft artifact snapshot helper. It requires
a strict descendant of the protected export root and disjoint export/state
roots before one bounded regular-file no-follow open, then compares actual
bytes to the expected SHA-256, writes `inputs/artifact` with checked `0755`
mode under a private provider-compatible attempt root with paired `outputs`,
syncs file and directories, and verifies staged bytes again. Cleanup retains the
stage on failure and requires a durable parent-directory sync before clearing
ownership. The focused spec is unrun. This helper is deliberately not called
from the fail-closed verifier until OCI isolation and result publication can
use that owned stage. Ancestor trust and separate worker credentials remain
necessary; the helper does not prevent same-user mutation of its stage.
Static review also found that the native bounded no-follow readers could
block on a FIFO before `fstat` rejected it. Their POSIX opens now use
`O_NONBLOCK`; a FIFO regression remains unrun under the verification cap.
An additional pure-Simple result-store reader now ingests only the fixed
`committed`, selected `receipt`, and raw `stdout.bin` leaves under the paired
output root. It applies bounded no-follow reads and the canonical result
parser, returning bytes explicitly labelled untrusted. Its focused spec is
unrun. The parent still needs authenticated worker isolation, V4 binding,
exact-ID OCI destruction/absence, and protected result-directory ancestry
before these bytes can become a success receipt.

## Fixed-fixture alternative

A Docker API attach stream established before container start can carry binary
stdout/stderr as framed bytes without using the engine log backend. For the
staged deterministic fixture, a protected expected byte count and SHA-256 can
prove the **observed** output matches the fixture. The attach protocol has no
terminal total-byte receipt: a clean disconnect at a frame boundary could
hide an additional suffix. Thus this path can qualify a fixed fixture only;
it does not replace the complete-output worker contract for arbitrary
programs. A direct API implementation must pin the daemon endpoint and full
container identity, reject TTY mode, parse all eight-byte frame headers and
payload lengths, distinguish read error from EOF, and verify destroy/absence
before claiming the fixture result. A pure-Simple bounded Unix byte-stream
owner, framed attach decoder, strict HTTP parser, and attach source now exist
as source drafts. The source requests `logs=0`, requires a caller-pinned
API version and full container ID, establishes headers before start, and
records transport EOF while explicitly leaving `output_complete=false`.
Caller-selected monotonic budgets bound header and capture reads. A new
timed Unix connect primitive bounds the initial local socket connection; it
passed a C syntax check but has no compiled Simple or live daemon evidence.
The host runtime adds one SIGPIPE-safe socket send: it accepts packed bytes or validated raw
`[u8]` slots, suppresses SIGPIPE, and returns a short or failed send to the
Simple caller. Astra found and corrected an initial representation mismatch
with `text.bytes()`; compiled byte-array lowering and the live Docker exchange
are still unverified. Socket reads use per-syscall
timeouts; writes have an aggregate monotonic budget. No protected controller
integration or live result exists yet. A fixed binary fixture comparator and
focused spec now check independent expected stream counts and digests, but
the spec has not run. The current OCI provider cannot qualify the live path:
its Docker CLI uses an ambient endpoint, inspect omits TTY and first-start
evidence, and destroy/recover can accept a durable tombstone without a fresh
exact-ID absence observation. No live qualification coordinator is wired to
this provider; its gaps remain an explicit admission block.
