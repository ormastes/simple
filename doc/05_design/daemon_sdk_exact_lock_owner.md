# Daemon SDK exact lock acquisition ownership

Scope: SDK mechanism only, based on release/1.0.0 a371c2e2728e5b4f222254c59502bf04945a94ea.
Publication/admission PRs 7462 and 7522 are inherited, not reimplemented.

## Accepted contract

DLOCK-01: `DaemonLockReceiptV1` contains path, PID, complete record and acquisition
success. `try_acquire_daemon_lock_owned` returns a denied receipt on contention,
entropy failure or create failure. `release_daemon_lock_owned` deletes only an
exactly matching record. An already absent path is an idempotent successful
release for an acquired receipt; a different record is refused.

DLOCK-02: `DaemonRunner` retains the receipt and uses it for shutdown. Repeated
shutdown of an old runner cannot remove a newer same-PID acquisition. Its legacy
`lock_pid` field remains available; it is not release authority.

DLOCK-03: legacy acquisition still writes the historical two-line PID/timestamp
record. Legacy release accepts only that format and matching positive PID;
it refuses generation-owned records, including a matching PID.

DLOCK-04: every SDK acquisition, stale-break and release uses the stable
`<lock_path>.break` kernel lock across judgment and filesystem mutation. The
SDK never removes that guard file. Attempts use timeout zero: contention is an
explicit refusal, with no retry/sleep loop. Stale detection preserves existing
PID liveness and partial-write grace semantics.

## Generation and trust boundary

Owned records retain the first two historical lines and append
`owned_generation_v1: <hex>`. The existing checked OS CSPRNG facade
`std.nogc_sync_mut.io.crypto_sffi.random_hex(32)` supplies 256 random bits;
missing/invalid entropy refuses acquisition. The nonce, not timestamp precision,
separates generations. This avoids durable counter reset/rollover metadata.
Collision probability is negligible, not a mathematical uniqueness guarantee.
No new runtime extern, compiler patch, entropy implementation or process-kill
policy is introduced. This is a compatibility extension to the historical PID
file, not a new general serialization or authentication protocol.

The lock directory is service-owned. All cooperating writers must honor the
stable guard; external unlink/rename of `.break` or arbitrary record tampering
is outside this mechanism. PID liveness does not establish process incarnation,
PID reuse safety, remote authority or recovery of uncertain effects. A copied
current receipt is the same capability, not a distinct owner.

## Focused evidence

`test/01_unit/lib/daemon_sdk/daemon_sdk_exact_lock_owner_spec.spl` uses real files
for all four contracts, including partial-record refusal and repeated shutdown.
`test/fixtures/native_daemon_exact_lock_owner/main.spl` independently exercises
lock-only same-PID generation replacement, legacy refusal/compatibility, and
kernel-guard contention through public APIs without invoking spool hashes or handler publication.

The lock-only native diagnostic passed once on 2026-11-07; see
[provider and runtime evidence](../08_tracking/test/daemon_exact_lock_owner_20261107.md).
The complete six-scenario SSpec, including runner shutdown, remains NOT_RUN.
No branch coverage, admitted SSpec, full-library or MCP qualification is claimed.
The existing native spool hash disagreement is independent: writer and ack
share `daemon_request_path_for`; its compiler/ABI cause is not repaired here.
Astra lead reviews exact source before push; root coordinates landing.

The provider audit is revision-bound. Ancestor `6c17f814aa0` already changed
nonpositive timeouts to a single nonblocking attempt across native POSIX and
Windows providers. Older blocking provider builds cannot qualify this contract.
The linked diagnostic was checked directly; the interpreter's reentrant lock
behavior cannot replace native contention evidence.
