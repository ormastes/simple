# Windows private readonly sharing V2

This is a distinct additive IO capability. It does not grant deployment,
execution, configuration or role authority, and does not change the V1
exclusive file owner. Host callers still verify their own fresh authorization
before effects and their final admission conditions afterward.

`std.nogc_sync_mut.io.windows_private_read_v2` exposes token-only
`WindowsPrivateReadRootV2` and `WindowsPrivateReadFileV2`. Read roots provide
current security, existing-child open, existing-file open and close. Read files
provide current security, bounded read and close. There are no create, write,
seal, publish or executable methods. Errors retain any acquired partial root
or file in `WindowsPrivateReadErrorV2` until close succeeds.

The same bounded native IO registry owns both profiles. Kinds 1/2 retain the
existing V1 semantics; kinds 3/4 are readonly roots/files. Every entry lookup,
IO operation, transition and close validates its exact generation and kind
under the same owner lock. A copy, forged V1 view or numeric-token reuse cannot
turn a readonly kind into mutation or close it through a V1 port.

Readonly ancestry requests LIST, TRAVERSE, READ_CONTROL and attributes with
`FILE_SHARE_READ | FILE_SHARE_WRITE`, while denying delete sharing. This admits
coexisting retained mutating parent handles without granting mutation through
the reader. Installed files request GENERIC_READ/READ_CONTROL with only
`FILE_SHARE_READ`. Multiple installed readers can coexist; writable or deleting
file opens cannot coexist. The no-reparse walk, fixed-volume admission,
protected DACL, owner/SID policy, identity and bounded ancestry checks remain
the existing security boundary. Read roots never create a child.

`windows_private_roots_same_directory_v2(writer, reader)` compares actual
retained V1-writer and V2-reader roots under the registry lock. Exact kinds,
generations and current ancestry/security must validate. The provider queries
both real volume GUIDs through bounded `GetFinalPathNameByHandleW` and compares
them together with `FileIdInfo` volume serial and 128-bit file ID. This avoids
equating cloned volumes by serial alone. A real mismatch returns `Ok(false)`;
query/validation failures return an error with both caller-owned roots retained.
Temporary release failures attach to the exact root whose validation queried
them. No identity metadata or additional role authority is exported.

## Sealed-stage handoff

`windows_private_publish_shared_read_v2(root: WindowsPrivateRootV1,
stage: WindowsPrivateFileV1, final_name)` returns
`WindowsPrivateSharedReadTurnV2(reader, stage, published_new, error)`; root
always remains caller-owned. The exact successful shape is empty error,
`published_new=true`, reader present and stage absent. Only then was the RW
handle actually closed and replaced by a verified readonly capability.

Before allocation/read, native code enforces the sealed stage's authoritative
maximum and actual size, at most 8 MiB. It captures the exact sealed bytes under
the owner lock, then performs the existing handle-relative no-replace rename.
Publication consumes the phase at the actual kernel effect. A proven collision
restores the original sealed stage and returns no reader, `published_new=false`
and empty error. The caller separately opens and verifies the protected final
entry; collision does not adopt bytes or grant new-publication authority.

After successful rename, the original RW handle is closed. A failed close
returns that exact V1 cleanup owner with `published_new=true` and nonempty
error. Its aliases cannot write or publish. Once close is confirmed, the final
entry is reopened readonly relative to the still-pinned mutating root. The
provider compares exact volume/file ID, size, full captured bytes and current
protected security before issuing a reader. A new readonly metadata snapshot
is captured only after this comparison, avoiding reliance on deferred Windows
last-write timestamps as content identity. A replacement with another file ID
or changed content is rejected. Reopen/admission failures retain any live
reader or stage cleanup owner. `published_new` remains a historical effect fact
on errors and never means readiness. Close failures always remain retryable.

File flush/process-crash semantics are the existing profile. Power-loss
directory-entry persistence is unsupported. Generic readers are not writable
exec leases; any purpose-specific exec mutation remains a separate owner leaf.

## Source verification and fixture boundary

Status: **NOT_RUN**. No builds, native/bootstrap checks or old privacy campaign
were authorized. This source is not Windows qualification or deployment proof.

`rt_windows_private_read_v2_selfcheck.c` is a new authored native fixture. On a
fresh installed private root, it retains nine transitioned readers while nine
more are actually reopened, checks kernel readonly access and native cast
refusal, verifies collision preservation, injects a failed RW close, and
performs a real final-name replacement during close/reopen to require identity
rejection with cleanup retained. Its test-only wrappers do not alter production
behavior or fabricate successful kernel operations.
The fixture refuses compilation with NDEBUG so its actual operations/checks
cannot disappear in a release build. It also covers matched/distinct root
identity, kind refusal and real failed security-descriptor release attribution.

The Simple integration spec requires a separately installed root containing
`artifact.sdn` with bytes `private artifact\n`. It exercises simultaneous typed
readers, forged V1 mutation refusal and missing-child refusal. Missing fixtures
fail explicitly. Actual host deployment consumer migration and worker readiness
require their own reviewed integration and Windows evidence.
The Simple scenarios retain every acquired root/file, including partial error
owners, in module-level canonical slots before assertions. Only confirmed close
clears a slot; failed close remains reachable without invoking stale copies.
