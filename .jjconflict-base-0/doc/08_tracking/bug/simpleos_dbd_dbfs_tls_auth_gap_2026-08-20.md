# SimpleOS dbd DBFS, TLS, and authentication gap

Status: open, release-blocking for REQ-014 and REQ-016

The bounded `dbd` safety slice validates and replays its whole journal before
mutation, rejects malformed commands before journaling, and verifies exact
write/readback bytes. It has a configured digest-only credential provider and
bounded per-session authentication identity. Credentials are opaque
high-entropy tokens of 32-128 bytes, not human passwords. The provider retains
only a SHA-256 digest and never logs credential bytes. Authentication compares
both principal and credential digests across the full fixed width and closes a
session after four failed attempts.

`DbdMutableAuthRequestOwnerV1` now parses exactly one bounded RESP AUTH request
directly from authenticated TLS plaintext bytes. Its incremental state machine
supports split records and a coalesced first post-auth command without
rescanning or materializing the credential as immutable text. It admits only
printable bounded principals and 32-128-byte credential fields, hashes them
through `DbdAuthSession.authenticate_bytes`, and wipes its mutable principal and
credential storage in place on success, rejection, malformed input, overflow,
lockout, and close. Owner observations record the exact wiped credential length
and verify every retained byte is zero. Failed attempts discard coalesced bytes;
successful admission alone releases bounded trailing command bytes to
`DbdAuthenticatedRespIngressV1`. That fixed-capacity mutable ring frames RESP
incrementally, rejects repeated AUTH in the byte domain, wipes bytes on take or
close, and converts only an already-complete non-credential frame to immutable
text once for the canonical parser. Per-session receive/request/response
budgets remain authoritative, and authentication plus command replies are
sealed by the same TLS session.

This still does not advertise authenticated network readiness. No boot
credential source currently guarantees bounded, non-cached mutable secret
delivery into the configured provider. Simple arrays cross ordinary call
boundaries by value, so the provider cannot prove destruction of a caller's
boot-time source copy. `dbd_production_startup_blocker()` therefore reports the
exact first remaining reason,
`boot-mutable-credential-owner-unavailable`, rather than the now-closed wire
framing gap.

The DBD TLS record owner is now structurally wired without claiming service
readiness. `DbdTlsSessionV1` reuses the shared bounded application-record
stream and the existing SimpleOS TLS 1.3 AEAD record layer. It retains only
ciphertext framing remainder plus established traffic state, releases
plaintext frames only after record authentication, and commits each receive
sequence after that record authenticates. Malformed framing, buffer/fragment
overflow, forged tags, unexpected inner content types, and sequence exhaustion
fail the session closed without logging crypto details. DBD applies cumulative
plaintext-byte and response budgets after decryption. It feeds pre-auth bytes
only to `DbdMutableAuthRequestOwnerV1`, returns encrypted fixed success/failure
responses, and exposes post-auth bytes to RESP dispatch only after the session
identity is admitted. The shared TLS stream's fixed-capacity ring accepts legal
one-byte fragmentation without retained-prefix recopying; DBD authenticates all
framed records against the proposed sequence range and calls the mutable ring
owner's generation-bound `commit_authenticated(token, count)` only after every
record succeeds. Authentication failure rejects the pending token before the
session closes. DBD does not copy/reconstruct the private ring or commit a
partially authenticated proposal. `DbdTlsIngressV1.zeroize_plaintext_frame`
and its all-frame companion mutate authoritative nested plaintext storage
directly, without an extracted COW array. The complete-command frame likewise
exposes an in-owner wipe method; callers never extract and reassign its byte
field. Focused behavior observes the exact wiped byte count and zero retained
nonzero bytes. Traffic-key
references are cleared when the DBD session fails or closes.

No by-value DBD TLS compatibility wrapper remains exported.
One `DbdLiveClientSessionV1` owns the fixed ring, auth session, budgets, and
mutable command ring; socket ingress calls `live.tls.ingest`, proposal decisions
mutate `live.tls.stream`, and response sealing mutates the same TLS owner. This
avoids a 32 KiB stream copy per fragment or reply. Focused behavior coverage
checks one-byte ingress on one session identity, monotonically increasing byte
work, sequence commitment only at the final authenticated record, and no
pending proposal after commit.

Socket closure now has a typed DBD owner rather than fire-and-forget cleanup.
Listener and client descriptors remain owned after a failed `rt_net_close`;
each poll performs at most one retry, three failed attempts enter terminal
quarantine, and restart carries retryable/quarantined descriptors instead of
resetting their state. The active-connection lease is released only after a
verified client close. Listener lifecycle cancellation/failure is published
only after its descriptor closes and existing connection/worker leases are
zero; otherwise lifecycle and worker accounting remain intact for retry.

Production TLS remains blocked because repository inspection found no canonical
DBD/boot owner that supplies a certificate chain and private signing key to the
existing `tls13_accept` handshake. The other SimpleOS server path records the
same missing key-store/config-read boundary. A canonical typed entropy owner
does exist at `os.crypto.entropy.crypto_entropy_bytes`, but `tls13_accept`
bypasses it and calls legacy `random_bytes` directly, whose API cannot return
typed entropy failure. `Tls13ServerConfig` has no entropy-provider input, so the
DBD adapter cannot wire the canonical owner without inventing a parallel
handshake. DBD also has no per-target boot receipt proving fresh, non-stub
entropy. The capability ledger therefore retains
`tls_handshake_authority=BlockedCertificatePrivateKeyEntropyOwner`; this slice
does not invent a key store, readiness boolean, or entropy facade. The
record owner accepts only the suites its current record dispatcher genuinely
implements (AES-128-GCM and ChaCha20-Poly1305); AES-256-GCM is rejected rather
than falling through the record helper's AES-128 default. A typed
`Tls13ServerConfig` argument is the future provisioning seam and cannot bypass
the private auth/TLS/DBFS startup facts.

DBFS owner discovery is now typed rather than boolean. `DbdServer` resolves the
actual root `DriverInstance`; only the `DbFs` variant can construct its adapter.
The adapter supports an exact, bounded recovery read of an existing `/DBD.LOG`,
tracks open handles and generations, and quarantines short-read/close failures.
Restart releases its old driver reference but preserves quarantine state and the
non-secret failure reason; a restart cannot silently reset durable-recovery
evidence.
It rejects commit before opening or mutating the file. This is necessary because
the current `DbFsDriver.fsync` and `fdatasync` return `FsError.Unsupported`, while
`group_commit` flushes its `SharedWal` value but does not prove a backing-device
flush. Neither surface satisfies an acknowledged durable database mutation.
The read is currently diagnostic-only for an in-memory driver: device-backed
`DbFsDriver.read_bytes_handle` falls back to its in-memory inode copy after a
device read error, so the adapter rejects that path as
`dbfs-device-read-fallback-unverifiable` instead of treating stale bytes as a
restart/recovery oracle.

Required closure evidence:

- a DBFS transaction owner with atomic durable commit and crash-recovery tests;
- `DbFsDriver` fsync/fdatasync or an equivalent transaction commit that issues
  and verifies the backing `BlockDevice` flush, then exposes that owner through
  the typed dbd adapter without adding a caller-controlled readiness flag;
- a TLS certificate/private-key owner with key lifecycle, peer-authentication
  policy, typed entropy failure, and negative handshake tests;
- a boot credential source with bounded non-cached mutable buffers plus
  provider reload/revocation tests;
- a compiler-resistant mutable-buffer wipe primitive with optimized native
  disassembly/runtime evidence;
- optimized-native evidence that the mutable AUTH owner wipes all retained
  copies and that compiler optimization cannot remove the stores;
- x86_64, AArch64, and RISC-V native receipts showing the same protocol and
  recovery behavior without host fallback.

Performance/durability blocker:

- the post-auth fragmented-command copying blocker is closed structurally:
  `DbdAuthenticatedRespIngressV1` owns a 64 KiB fixed ring and head offset,
  performs one write plus one incremental framing step per accepted byte, and
  one copy only when taking a complete frame. Focused one-byte-fragment behavior
  checks total owner work below `3 * frame_bytes + 1`; incomplete input is
  neither concatenated nor rescanned. Optimized-native timing remains part of
  the general target receipt requirement above, not a known quadratic path;
- the current VFS journal seam has no crash-atomic append-plus-sync primitive;
  `persist_journal_line` therefore rewrites and rereads the complete journal
  for every `SET`/`DEL` before acknowledging it;
- with the current 1 MiB journal bound, one mutation performs up to 1 MiB of
  write I/O plus 1 MiB of verification read I/O, and filling the journal is
  O(total-journal-bytes squared) across successive mutations;
- this bounded fail-closed fallback is not performance evidence. Closure needs
  an owner-provided append/sync or transactional DBFS commit primitive plus
  latency, throughput, crash-cut, and recovery measurements on every target.

Until all evidence exists, `DBD_CAPABILITY_STATE` must remain blocked and the
daemon must fail closed instead of accepting network clients.

## tls13_accept entropy bypass closed 2026-08-21 (record stays open)

This record named the bypass exactly: "A canonical typed entropy owner does
exist at `os.crypto.entropy.crypto_entropy_bytes`, but `tls13_accept` bypasses
it and calls legacy `random_bytes` directly, whose API cannot return typed
entropy failure." `src/os/tls13/server.spl` drew *both* the ServerHello random
and the server ECDH **private scalar** as `random_bytes(32u64)`, whose return
type is a bare `[u8]`: a short, empty, or all-zero draw was indistinguishable
from a good one and would have been used as a private scalar, yielding a
predictable shared secret and therefore predictable traffic keys.

Fix (`src/os/tls13/server.spl`, smallest correct diff, no new key store, no
readiness flag, no parallel handshake): `tls13_accept` now draws both secrets
through `crypto_entropy_bytes` and fails the handshake closed with
`server_entropy_unavailable` on a typed entropy error. Each draw is then
admitted by the new `tls13_server_entropy_admits` — exact 32-byte length, at
least one nonzero byte — failing with `server_entropy_wrong_length` /
`server_entropy_all_zero`, and the two draws must differ
(`server_entropy_repeated_draw`). All checks run before
`prepare_server_handshake_from_client_hello_record`, i.e. before any key
derivation. `os.crypto.random.random_bytes` is no longer imported here.

Evidence — `test/01_unit/os/tls13/server_entropy_owner_spec.spl`:

`SPEC FILE VERDICT: test/01_unit/os/tls13/server_entropy_owner_spec.spl outcome=OK declared>=12 executed=12 passed=12 failed=0 skipped=0 dropped=0`

No regression in the existing accept suite: `test/01_unit/os/tls13/server_accept_spec.spl`
reports `Results: 32 total, 29 passed, 3 failed` **both with and without** this
change (verified by reverting `server.spl` and re-running); those 3 failures are
pre-existing in the `..._with_server_material_for_test` CertificateVerify path
and are not caused by, nor fixed by, this change.

**New concrete blocker found while proving the fix — the entropy platform extern
is unbacked.** A live `crypto_entropy_bytes(32)` draw in the interpreter fails
with `semantic: unknown extern function: rt_entropy_fill`. `rt_entropy_fill` is
declared at `src/lib/nogc_sync_mut/crypto/entropy_platform.spl:7` and has **no
runtime backing anywhere in the tree** (`grep -rn rt_entropy_fill src/` returns
only that declaration and its single call site), so the canonical owner cannot
currently draw on any path — it traps rather than returning a typed `Err`. This
is why the spec above deliberately does not exercise a live draw; it covers
every path that returns before the extern is reached, and the omission is stated
inline in the spec rather than hidden. Closing this needs a real backing for
`rt_entropy_fill` (e.g. `getrandom(2)`) plus the per-target boot receipt this
record already demands.

`DBD_CAPABILITY_STATE` therefore stays blocked and
`tls_handshake_authority=BlockedCertificatePrivateKeyEntropyOwner` is retained:
the certificate/private-key owner, the boot credential source, the DBFS durable
commit owner, and the wipe/native receipts in the closure list above are all
untouched by this change.
