# Retained host SSH identity storage V1

Status: SOURCE_AUTHORED_NOT_RUN. Pinned implementation context:
`60faaa5c097c17ffd74618cd9f2830631cd463d0`. New source is isolated under the
assigned `/tmp` artifact tree; no existing owner, runtime, index or branch is
modified. Storage is opened before entropy/key generation by its consumer.

The public owner is opaque. The `host_identity_store_*_v1` functions open,
read, publish, close, query a validated transport path and preflight transport
support. Physical layout is `root/journal/<64 lowercase hex>.key|.hosts|.profile`.
Only nonempty bounded UTF8 without NUL is published, up to 65536 bytes; reads
are bounded independently. The shared key codec owns OpenSSH private-key,
public-wire and known-hosts pin validation. Existing bytes must pass that codec
and exact expected identity checks before the upper layer accepts reuse.

The profile role is distinct from both key and known-hosts roles. Storage does
not parse SDN or reinterpret suffixes. The consumer strictly validates its
ServerSshProfileV1 record and derives the profile stem from canonical SDN bytes.
All three roles share the 65536-byte UTF8/NUL bound and no-replace semantics.

Copying an owner copies a private generation reference. Existing mutex gates
serialize a canonical per-platform registry, and slots are never reused. Every
descriptor/handle capability is recorded before fallible observations. Invalid
argument turns preserve the canonical owner's cleanup_pending state. Linux is
explicitly restricted to the canonical main thread. Its existing genuine
retained-procfs process-origin guard runs before mutex initialization, locking
or registry access, including for copied close. It verifies procfs mount and
self/thread-self magic-link provenance, not numeric PID equality alone. The
numeric PID remains a stage label/additional check; inherited PID1 in a nested
namespace cannot use it as authority. The dependency retains its own process-
lifetime procfs resources and is not closed by this adapter.

Transport preflight checks canonical origin and actual current protected root
without a target read or filesystem publication. Consumers call it before
secret generation/publication for transport setup. Linux succeeds only for a
current actual owner. Windows returns `identity-store-transport-projection-unavailable`
only after that actual integrity check; native/integrity errors remain their
distinct errors. It cannot currently prove a transport-safe resolved path via
the opaque provider. Logical key generation/storage remains separate.

Path queries read and validate the actual existing protected target first and
discard that private byte result. Linux returns its validated diagnostic path.
Windows returns the same dedicated projection limitation only after positive
file validation; absent files and actual read/native failures remain distinct.
No native GLOBAL??/GLOBALROOT prefix is stripped or reinterpreted as an ordinary
drive or /GLOBAL?? SSH path. Existing provider root admission is preserved,
including its honest refusal of unsupported native spellings. No C-only rule
is added. The consumer retains the owner through any supported SSH launch.

## Platform ownership

Linux x86_64 and aarch64 use existing retained-file libc declarations plus
ordinary `mkdirat`, `fchmod`, `linkat`, `unlinkat`, errno and PID declarations.
There are no new runtime exports. Retain `/` and every nofollow directory
component; check actual statx owner/type/mode/device/inode and parent/name
binding before operations. Existing ancestors must belong to root or the actual
effective user and forbid group/other write. Sticky shared directories are not
trusted. The final root and journal require current-user ownership and 0700;
only the final root and journal may be newly created, each with 0700 before
private data exists. Parent directories are actually fsynced on admission.

Create a fresh O_EXCL/O_NOFOLLOW/CLOEXEC 0600 stage. Record its fd, verify actual
regular type/effective UID/one link/empty size, set 0600 on that exclusively
created inode before bytes, and verify it again. Write bounded bytes and fsync
the retained file. Compare the retained source and its actual stage name, then
linkat within the same retained journal directory with no replacement flags.
A genuine EEXIST becomes Existing only after inspecting the actual target as a
current-user 0600 regular file with one link and bounded size. Other failures
never imply existence or absence. Successful publication additionally compares
the destination inode with the staged inode, unlinks only the exact stage
binding, and fsyncs the journal. Published/file_synced/namespace_synced reflect
this invocation's confirmed calls. Existing has both durability flags false.

Read with nofollow openat and pread. Check file UID/mode/type/link count/size
before reading; compare complete inode/size/mtime/ctime and final-name identity
after reading and recheck the directory chain. Only an actual ENOENT plus a
current directory chain establishes absent=true. Generic open/metadata errors
have bytes=None, absent=false and require owner cleanup. Unsupported POSIX
systems and unsupported Linux architectures explicitly refuse.

Windows reuses the existing WindowsPrivateRootV1 and exactly one actual
WindowsJournalStoreV1. Open a protected existing parent and acquire/create the
final private child through child_directory, retaining every error's cleanup
root/file capability. Acquire the actual journal and verify belongs_to(root)
and actual ancestor privacy. Journal read supplies proved absence; failure to
open a private file is never treated as absence. Native journal publication
already stages protected files, flushes the file, checks identity and performs
atomic no-replace rename. Only its successful publication sets file_synced.
Its namespace lacks directory flush: namespace_synced is always false. This
honestly implements the supported minimum without claiming power-loss safety.

## Error and close disposition

NotAttempted means this invocation did not attempt target publication. Existing
means an actual protected target remained untouched. Published means confirmed
no-replace publication. Uncertain preserves the canonical stage/native pending
cleanup and forbids further operations until cleanup; no destination deletion,
overwrite, compensation or silent retry resolves it. Durability flags do not
carry over from an existing file or prior invocation.

Windows cleanup closes journal, pending error files, final root, then parent,
retaining failed native capabilities for an actual retry. Linux cleanup removes
only a stage name whose inode equals the retained stage descriptor's identity;
it never deletes the destination or a substituted inode. Each fd slot is
consumed before close. An uncertain close is never retried using that raw fd.
If all slots were consumed but a close failed, owner=None/completed=false/error
reports that exact disposition. A remaining exact stage obligation retains the
owner. Close never removes a published key or pin. Upper layers preserve both
the error and an unresolved owner in their cleanup reply.

## Threat boundary and evidence

Trust excludes malicious code running as the same OS user, administrators/root,
or a compromised kernel. Private directory ownership/ACLs prevent other users
from substituting staged names or targets. No path-only API can prevent a
trusted same-user process from changing its own namespace between checks.
TODO: integrate stronger OS keystore/hardware-backed private-key protection as
a separate reviewed feature; this adapter makes no such protection claim.
Private bytes never appear in errors, logs, SDN or test captures.

The authored actual-fixture spec and mirrored manual cover persisted winner,
distinct profile collision/role independence, no overwrite, alias lifetime,
reopen, unsafe ancestry and cleanup truth after unsafe target reads. Pure
production-helper examples cover exact leaf grammar. Genuine PID-namespace and
worker-thread refusal procedures remain manual NOT_RUN, not simulated PASS.
No native runs, builds, tests, docgen, fault injection,
concurrent race proof, perf measurements or coverage percentage are claimed.
