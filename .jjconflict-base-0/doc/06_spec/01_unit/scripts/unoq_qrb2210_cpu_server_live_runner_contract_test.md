# UNO Q CPU server live-runner contract

The operator runs `sh scripts/check/run-unoq-qrb2210-cpu-server-live.shs --self-test`
before any physical-board campaign. This negative-only test never invokes ADB.
It proves synthetic non-SimpleOS and GPU-selected receipts are rejected.

Physical execution is permitted only under `/tmp/unoq-server-matrix.lock` and
must name the ADB serial explicitly. Before any board read, the runner requires
the current-source compiler admission receipt, dirty-inclusive source manifest,
and exact admitted AArch64 server ELF. The runner rejects Debian, requires the
SimpleOS identity marker, exact filesystem server/provider/provenance hashes,
CPU-only selection with no GPU library or provider use, HTTP filesystem-byte
equality, and authenticated database write/restart/read persistence.
Acceptance also requires a fresh reboot, clean shutdown, explicit forced-CPU
selection, and negative evidence that accelerator libraries/providers, GPU
submission, and device readback were unused.

The returned receipt is bounded and pointer-free. The host parent validates
every field and hash before granting acceptance. This manual does not claim a
physical-board pass; no live run was performed while creating it.

When the serialized collector owns the lock, it passes inherited descriptor 9;
the runner validates `/proc/$$/fd/9` resolves to the canonical lock path. A bare
environment claim is insufficient. The host captures the live server's process
maps and file descriptors and rejects accelerator libraries, `/dev/dri`, KGSL,
Adreno, or render-node use. It hashes server/provider bytes before and after the
fresh-reboot campaign and verifies remote receipt cleanup before publication.

For both boot phases, the host binds PID executable bytes and command line to
the admitted server and `--cpu-only`, then captures maps and file descriptors.
The host sends the HTTP request, compares independently observed filesystem and
body bytes, and performs authenticated DB write/read plus post-reboot read.
Credential bytes come from host entropy, are scanned for retention, removed on
both sides, and covered by failure/signal cleanup.

The host owns a bounded credential byte scan over the declared evidence,
server-state, and temporary-directory roots and binds its
hash. Terminal output carries phase, mutation, and checked-cleanup state;
cleanup failure overrides the original result while scrubbed diagnostics are
retained. HTTP requires exact 200 status, unique numeric length, and byte-exact
body/hash. DB requires exact authenticated grammar, generation, commit hash,
value hash, and post-reboot equality. Boot identity must match a detached
signature verified under the repository-pinned local trust root. The collector
snapshots/hashes the CPU runner, retains its exit, propagates combined CPU/GPU
outcome, and refuses collisions. Protocol sabotage executes without ADB.
