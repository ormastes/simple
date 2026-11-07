# Retained private credential V1

Cycle 5 source provenance: virgin namespace observation ports
`lu_initial_namespace_v1` verbatim except its symbol name from
`/home/yoon/dev/simple-local-unix-gateway-owner-20261107/src/runtime/runtime_local_unix_v1.h`
(lines 37–46), verified whole-file SHA256
`33545b151e65ec1b3added3b8bb96ad9c2a9341a381e3281428eacdbcb35605f`.
It opens the namespace handle O_RDONLY|CLOEXEC, requires fstat plus fstatfs
NSFS_MAGIC and NS_GET_NSTYPE ioctl equal to CLONE_NEWPID, and checks exactly
one close before publishing origin. The kernel sched header supplies clone
constants when libc GNU-extension declarations are disabled. Existing CAS,
Ready, established stat comparison and permanent quarantine remain unchanged.
An isolated exec-only test redirects only the initial open to a real regular
file and exercises actual filesystem/ioctl rejection and single checked close.
Restoring the open target never resets failed initialization. Actual namespace
transition qualification remains BLOCKED; this source has not been compiled.

Established Ready origin stat failure or observed mismatch permanently stores
phase 3 Quarantined. Restoring stat availability or the prior origin values
never re-admits this process-local registry. Initial acquisition failure keeps
phase 1 Initializing instead. Entry checks quarantine before locking and again
after acquiring the mutex, before any owner access. A post-acquisition refusal
uses only that same invocation's ordinary matched unlock; no extra origin
syscall/recheck is added to normal unlock. The operation boundary is public
entry/lock acquisition, not continuous origin polling inside an admitted call.

Origin identity is the actual getpid plus device/inode from
`stat("/proc/self/ns/pid")`, checked before any registry/mutex access. A
compile-time assertion requires lock-free `atomic_int`. The sole CAS winner
publishes Uninitialized→Initializing, writes immutable PID/device/inode, then
release-publishes Ready. Acquire readers refuse Initializing without spinning
or reading partial fields. Namespace stat failure refuses with IO error;
observed origin mismatch refuses as fork-token. Failed/interrupted initialization
is never reset or adopted. This blocks equal numeric PIDs across PID namespaces,
including inherited PID 1, instead of relying on PID alone.

Source prevention includes isolated exec-only injected namespace-inode mismatch
and Initializing-shape assertions. These are labeled contract tests and do not
claim actual namespace creation/transition. Actual namespace qualification is
**BLOCKED** pending a separately authorized fixture; no privilege is requested
or used for namespace operations here.

Native prevention qualification has two explicit scopes. Default/`--privileged`
requires an isolated UID-0 fixture to check an actual foreign-UID file.
`--unprivileged` retains all other real native assertions and labels its result
as subset-only, with foreign-UID **BLOCKED**. No automatic elevation or implicit
successful skip is permitted. Neither mode has been executed at this checkpoint.

Leaf opens also use O_NONBLOCK so a substituted FIFO cannot wait for a writer
before regular-file validation. Cryptographic entropy uses nonblocking
getrandom and fails if unavailable. Publication snapshots both borrowed input
buffers before validation or writing, preventing caller-buffer changes from
altering the validated payload.

Status: **IMPLEMENTED_SOURCE / AUTHORED_UNRUN**. Root-authorized Linux OS boundary; qualification remains pending. Existing RetainedFile and RetainedDirectoryOwner behavior is unchanged.

`RetainedPrivateCredentialV1` contains only a positive opaque native generation token. A fixed 32-slot per-process registry owns descriptors, initial bytes/identity and authoritative Open, Published, Uncertain or Closed state under a mutex. Tokens increase monotonically without wrap; closed slots may be reused only under a new token. An inherited-process PID guard rejects fork copies before touching the inherited mutex. Tokens cannot be serialized, restored after restart, used as diagnostic PIDs, or accepted from peers as authority.

The native owner acquires its own absolute path through no-follow, close-on-exec component opens. Components reject dot aliases, repeated separators and unsafe leaf syntax. Every ancestor is root/current-EUID owned and not group/other writable, except root-owned sticky directories. The final directory is exactly EUID-owned mode 0700. Initial file is no-follow regular, EUID-owned exactly 0600, single-link and 1–512 bytes. The owner retains its actual inode and checks metadata, contents and anchored directory entry before publication.

Initial bytes are immutable `<nonce> TOKEN` with optional one LF; nonce is exactly 32 lowercase hex characters. Configured ready bytes are exactly `<nonce> 127.0.0.1:PORT <token> <diagnostic-pid> <service-incarnation>` and one LF. Initial nonce/token are bound exactly; port is canonical positive decimal within 65535, PID is positive decimal diagnostic data, and service incarnation is 32 lowercase hex characters. Parent server validates its actual endpoint/incarnation. This module never turns a descriptor/PID into workload identity or readiness.

Publication transitions out of Open before any attempted publish, including invalid ready arguments. A cryptorandom exclusive mode-0600 temporary file under the retained directory receives at most 512 bytes and is synchronized. Linux `renameat2(RENAME_NOREPLACE)` publishes only the sibling `<initial-name>.ready`; no overwrite, path-write, link or mutex-as-CAS fallback exists. The directory is synchronized; final bytes, mode and inode are independently reopened under the retained directory and compared against the retained temporary descriptor. Initial file remains unchanged. Failures retain the native owner in Uncertain and require a fresh startup generation; existing ready winners are never deleted. Close/reconnect never deletes ready records.

Close retains only verified temporary cleanup, invalidates all native descriptor slots before OS close, and never retries a consumed Linux close error. Success closes the registry entry. A consumed error returns code -14, consumed=true/completed=false, and keeps an Uncertain token with no descriptors for diagnostics. Repeated copied close has no descriptor effects; a reused successor token is unaffected. Temporary cleanup never addresses the ready name.

The canonical retained_file facade owns all bounded buffer conversion. Open/read/mutation/state turns retain the token even on failure. Operation completion/consumption derive from the same locked operation result; subsequent state observations may downgrade but never upgrade it. Six exact native exports are registered in `scripts/check/check-rt-dual-implementation-ratchet.shs`; no broad exclusion is added. They are designed C-owned OS primitives under explicit repository-owner approval, with the pure Simple facade/types providing the public policy boundary. Windows, macOS and other hosts return unsupported explicitly; no Rust-seed or raw-path fallback is introduced.

Required prevention evidence is authored in the native selfcheck and Simple ownership spec/manual. ABI pointer/host-map audits, native compile, selfcheck, facade spec and real configured server integration must run on an admitted producer/backend before any PASS, readiness or release qualification. No such claim is made by this source change.
