# Windows V6-only protected setup, journal-ready publication and reader

Status: SOURCE_AUTHORED_NOT_RUN. Eleven authored cases are NOT_RUN. No native,
compiler/link, provisioning, service, network or performance campaign ran.
Authoritative restart/strict-stop contract:
`/tmp/host-service-auth-v6-mode-schema-20261115-r2.sdn`.
Legacy V5 is separate and unchanged. No V5 bearer conversion, SSH identity
reuse, plaintext secret frame, fixed setup+.ready publication, second journal,
ready pointer, lease recreation or new runtime export is introduced.

## Private setup and public pin

The administrator selects a fresh setup path under an EXISTING protected
credential parent. Canonical SDN plus LF is bounded512 bytes and has exactly8
fields: version6, kindhost-service-auth-setup,
generatorhost-service-auth-setup-v1, entropySourcesosix-os-csprng,
publicationUid(lowerhex32), secret(lowerhex64), uidBytes16, secretBytes32.
The public installed pin is SHA256 of the exact canonical private setup bytes
including LF. The secret never appears in ready metadata, public turns,
diagnostics or network frames.

The actual setup producer acquires protected writer AND read roots and proves
their identity before calling sosix_random_hex(16) and (32). No supplied key,
entropy flag, old bearer or SSH credential is accepted. Existing crypto_sffi
checks the OS-provider result; Windows runtime_native.c:214 uses
BCryptGenRandom and refuses provider failure without a weak Windows fallback.
Shape is not entropy proof. The protected generator record is provenance
within the trusted administrator/account boundary, not attestation against an
administrator or same-authority code compromise.

## Existing Host lease selects immutable ready data

The actual already-owned Host journal supplies parent.lease. Exact bytes are
`DISTRIBUTED-OPERATION-LEASE-V2\n{nonce64}\n{authorityDigest64}\n`.
The reader rejects any other header, width, case, line count, authority or LF
spelling. SHA256 of these exact bytes selects the sole ready record:
`host-service-ready-v6/<leaseDigest>.sdn` inside that SAME Host journal.
No new pointer/journal, previous-key fallback or fixed ready replacement exists.

Public ready SDN plus LF is bounded512 bytes and has exactly9 fields:
version6, kindhost-service-auth-ready, publicationUid, setupDigest, endpoint,
servicePid, serviceIncarnation, hostLeaseDigest and hostAuthorityDigest.
There is NO secret. Endpoint is the actual bound127.0.0.1 port, servicePid is
sampled inside the producer, and incarnation comes from the actual retained
fresh service. PID/endpoint and lease equality are DATA, not OS listener or
Host liveness authority. Windows normal journal close leaves parent.lease;
Linux close differs. A matching stale file after close proves no live Host.
Per-connection authenticated challenge/nonce consumption is still required.

Strict bounded SDN, complete key/type checks and exact canonical reencoding
reject extra/duplicate fields and aliases. Actual setup pin/UID, selected
lease, expected Host authority and actual incarnation are checked together.
New Host lease with missing ready means unavailable, never old-ready fallback.
An existing reader never silently rotates to the new lease/incarnation.

## Retained reader interface and actual custody

Generic module: std.nogc_sync_mut.io.host_service_ready_reader_v1.
Opaque HostServiceReadyReaderV1. Full function prefix is
host_service_ready_reader_. Open signature:
`open_v1(setup_path,expected_setup_digest,host_deployment_root,expected_host_authority_digest,expected_publication_uid="")`.
It returns OpenTurn(owner?,ready,error). Current returns Result. Endpoint,
incarnation, expected_service_pid, ready_digest and host_lease_digest getters
return Result DATA after actual current validation. Close returns
CloseTurn(owner?,completed,error).

The configured Windows leaf opens the actual private setup read root/file,
and independently opens the actual configured protected deployment root.
It traverses FIXED child_directory("journal"), then
child_directory("host-service-ready-v6"), and opens only the selected digest
leaf. No raw concatenated child authority, directory equality between
independent setup/Host roots, or textual deployment-root admission is claimed.
The configured root locator becomes custody only after actual native ancestry,
ACL, kind, identity and read-profile checks. Other platforms refuse this NEW
facade; old readers and modes are unchanged. Native GLOBAL prefix and Unicode
parent spelling survive an exact byte-offset last-separator split.

Each current check freshly opens parent.lease under the actual journal root,
reads at most512 bytes and POSITIVELY CLOSES that temporary file before any
network or MAC work. It repeats that short read/close after setup/ready reads.
The exact selected digest/authority must remain unchanged. No deny-delete
lease handle remains across a successful current/MAC return. A short read
can block replacement/startup; close failure retains the exact temporary
file and quarantines/refuses, with no retry/liveness promise. Missing or changed
selector has no fallback. All root/file privacy is checked before/after reads,
and exact retained setup AND public ready bytes are compared every use.

A canonical native-thread registry holds the actual resources; opaque values
carry private slot/generation only. Bounds32 active/100000 nonreused lifetime
slots. Existing native-mode and Windows canonical-thread guards run before
every entry, including tombstones. Aliases share first error, quarantine and
positive cleanup. Close is independent of current validity, releases the
temporary selector first, then files and child-to-parent roots, clearing only
on actual positive close. Closed tombstones drop cached secret bytes, metadata
and root capabilities. No managed-memory zeroization or native latency claim.

## Key-private MAC surface

Only trusted IO implementation code can call package-visible
mac_request_v1(owner,context,exactcanonicalrequest),
verify_server_v1(owner,context,role challenge|reply,body,tag),
server_tag_v1(owner,context,role challenge|reply,body), and
verify_request_v1(owner,context,exactcanonicalrequest,tag).
No arbitrary app/wire signing RPC or raw key getter exists. Current checks
bracket every MAC operation; actual ready incarnation must match context.
Accepted shared pure helpers validate role, both nonces, exact canonical
command digest/body and request incarnation. The key is exact64 ASCII hex
TEXT bytes as the accepted HMAC contract specifies, never implicitly decoded.
Pure data helpers alone cannot mint a retained reader.

Actual challenge freshness, single-use connection, Host authority/effects and
listener lifecycle belong to the canonical connection/server owners. Wrong
listener never receives this secret. No ordinary current relaxation or final
reply permit exists: if selector changes during stop reply drain, delivery/
verification is Unknown. The server retains actual Host-close outcome and
cleanup carriers internally; it must not replay, reconnect or return ready.
If the selector remains, normal reply signing can proceed after Windows Host
close, but matching selector data is still not Host liveness.

The accepted rt_black_box source repair is dependency PR#9579,
commit9bb319f981bfed6f6517ea790dbd04532d13f0c3. Its merge and these source
methods establish no installed-runtime correctness or constant-time timing
qualification. Common pure auth/frame/operation owners are separate reviewed
dependencies; this bundle does not duplicate their transcript or MAC logic.

## Actual setup publisher

Module std.nogc_sync_mut.io.host_service_auth_setup_v1 exports administrative
setup open_v1(setup_path), step_v1(owner,cancel=false), close_v1(owner), full
prefix host_service_auth_setup_. Opaque HostServiceAuthSetupOwnerV1. Turn:
owner?,phase,setup_publication,completed,cleanup_pending,publication_uid,
setup_digest,error. Derived path/name bounds precede root/entropy effects.
Actual writer/read pair is checked before OS random. Existing private
stage/write/seal/NO_REPLACE/adopt-read/readback primitives publish the one
private setup file. The setup path is never converted to a legacy credential.

## Ready publisher borrows the ONE actual Host journal

The same module provides package-only trusted server IO
host_service_auth_ready_publish_open_v1(journal,setup_path,pin,actualendpoint,actualincarnation),
step_v1(owner,journal,cancel=false) and public cleanup close_v1(owner,journal).
HostServiceAuthReadyPublishOwnerV1 is opaque. ReadyPublishTurn has exact
journal, owner?,phase,ready_publication,ready_digest,completed,cleanup_pending,
publication_uid,setup_digest,error. Caller retains the actual canonical Host
domain/journal; no journal/writer/store is stored inside the producer registry.
Only a small binding digest of actual root/authority/lease/health is stored.
Returned journal is the exact supplied carrier, including native publication
pending owned by its original store. Cleanup never closes or reopens it.

The listener bridge supplies actual bound local_addr and retained incarnation;
raw endpoint input is trusted IO data, not wire or app authority. Actual
GetCurrentProcessId is sampled inside this leaf. The producer retains/validates
actual private setup read custody. It freshly reads parent.lease through
existing distributed_operation_journal_read_required_v3, validates exact
owner lease/authority, publishes the derived immutable key through existing
publish_v3 and reads it back through the SAME owner. All existing health,
revision, writer/current-lease and native pending checks remain authoritative.
No separate writer, directory creation framework, ledger or publication API.
Parent server reopens via the actual configured deployment traversal and
compares actual ready_digest/startup lease/authority/incarnation/endpoint.

Both producer profiles share bounded canonical IO resource lifecycle only;
setup has its credential writer, while ready has NO writer and uses the
borrowed actual Host journal exclusively. Native modes/thread guard precede
lookup. Publication becomes unknown BEFORE its native call; only positive
result becomes published, definite collision conflict. Unknown/conflict is
never replayed/overwritten/deleted. Known unpublished setup stages alone use
existing exact-stage-discard. Published/uncertain setup targets are preserved.
Ready publication cleanup stays with the original journal, not this registry.

Every returned partial native carrier remains owned. Completed means positive
publication/readback plus this producer's own actual cleanup closed with no
first error; it is NOT Host close or service liveness. Cleanup_pending means
the producer still needs exact private resource cleanup. Public UID/pin/ready
digest/history survive failure even after ownerNone; unknown/partial never
turns into completed. Cleanup is allowed after Host close with the original
journal binding and does not read/publish it. First errors are sticky. Closed
aliases retain only bounded binding/public history, not secret/request/path
buffers. No crash-WAL, power-loss directory durability or OS-fault guarantee
is added beyond existing primitives.

## Source evidence and limits

Nine pure cases exercise production path/setup/ready/endpoint/lease/key
helpers. One actual Windows reader fixture requires an externally provisioned
private setup and selected ready in the real protected Host journal. One
explicit administrative native fixture would publish a fresh setup if run
against an operator-selected target. All eleven are NOT_RUN. Published
immutable artifacts are intentionally not deleted by fixture cleanup.
Native faults, selector replacement races/startup blocking, borrowed-journal
ready publication plus real listener composition, actual MAC network exchange,
compiler/link, latency/RSS and full Controller/Host integration are NOT_COVERED.
Shared server/app, V2 primitives, runtime, namespace/stdin/SSH files remain
untouched by this owned source bundle.
