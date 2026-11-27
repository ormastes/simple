# Retained paired SSH identity projection V1

Status: SOURCE_AUTHORED_NOT_RUN. Additive source copies are isolated under the
assigned projection artifact. Landed R2/PR9485, immutable artifacts, worktrees,
index, native owners and runtime exports are preserved. This implements the
frozen begin/step/paths/close interface; no OpenSSH process is launched here.
Independent source review and actual Windows Service interoperability remain
required before claiming integration or runtime qualification.

## Ownership and interface

`host_identity_ssh_projection_v1` exports opaque HostIdentitySshProjectionV1,
HostIdentitySshPathsV1 data, owner-bearing acquisition/cleanup turns, and the
four frozen operations. The opaque value wraps a platform child identity; its
constructor and numeric fields remain private in the actual store composition.
Neither paths, SID strings, decoded records nor caller booleans construct it.
The separate pure types module validates exact key/hosts roles through the
existing store grammar, rejects .profile in either slot, and defines only the
two path data fields. The two digest stems need not match.

The existing per-platform store registry owns up to eight concurrent projection
child states. There is no second root/store authority registry. A fully closed
slot may be reused only with a new checked monotonic generation. Copied owners
therefore cannot regain readiness when a slot is reused. Generation exhaustion
and the actual concurrent bound refuse explicitly. Linux consumed-unconfirmed
close tombstones are never recycled. Existing R2 APIs retain their semantics;
Windows generic path/preflight still report their existing limitation.

Begin checks the actual current supplied store and exact leaf roles before
reserving a canonical child. It opens no files and publishes no key, pin or
profile record. Step performs one bounded acquisition or cleanup phase. An
actual supplied-store mismatch quarantines the original projection and returns
that original cleanup owner. It cannot substitute another store or erase the
original obligation. Paths require Ready plus immediate complete proof;
failure permanently starts cleanup and returns the actual failure. Asking for
paths before Ready also invalidates the child; consumers use step readiness.

Projection close and cancellation invalidate paths before native retirement.
Store close marks the parent closing first, then advances child cleanup before
the journal/root/ancestor resources. Each retry advances one retained child
phase, preserving native retained errors instead of masking them as progress.
Successful intermediate cleanup uses the explicit pending marker. Native
release failure retains the exact remaining owners. No source operation here
silently recreates a failed projection or reactivates namespace readiness.

## Linux

Every entry uses the existing genuine procfs origin/main-thread guard before
mutex/registry access. Begin reserves the canonical child; the next two phases
open the actual key and hosts names O_NOFOLLOW/CLOEXEC/NONBLOCK, retaining each
readonly descriptor before metadata observation. Actual UID, 0600 regular type,
one link, 65536-byte bound, inode/device and timestamp/size identity are checked.
Ready/path/continuation recheck the full retained parent/name directory chain,
both retained files and both actual names against their original snapshots.
Paths are diagnostic ordinary Linux spellings under the same root/journal.

Linux makes no Windows sharing guarantee. The trusted same-user/root/kernel
boundary from R2 remains explicit. Same-user mutation between checks is outside
that boundary; observed drift still permanently invalidates the projection.
Cleanup consumes a child fd in canonical state before one close call. It never
retries an uncertain raw fd and propagates consumed-unconfirmed status. Parent
cleanup retains its own descriptors until child descriptor obligations are
drained. No published destination is deleted.

## Windows

The first supported service projection requires the actual store to have been
opened with explicit `\GLOBAL??\<drive>:\...` spelling. Ordinary-drive generic
storage remains unchanged; projection does not convert it into global proof.
The agreed lower dependency is `windows_service_logon_namespace_v1` with the
actual WindowsServiceLogonNamespaceOwnerV1, zero-argument open, incremental
step, current, candidate_path and owner-bearing close operations. Its source is
independently owned/reviewed; this artifact neither copies nor modifies it.

The child reserves ownership before namespace acquisition. Actual admission
requires the producer's Service5 token/logon/process/boot/no-impersonation and
protected DOS map/link/global-target proofs. Candidate_path supplies ordinary
drive path data only. The projection opens an actual WindowsPrivateReadRootV2
at that candidate, then proves equality with its actual store writer root using
windows_private_roots_same_directory_v2. Only afterward does it open the fixed
journal child and both exact existing key/hosts files with maximum65536.
Every partial read-root/file error's cleanup capabilities are attached to the
same canonical child before its failure is reported.

Ready/paths/continuation revalidate actual namespace/current candidate, writer
root equality, both retained read roots and both retained read files. The
candidate must remain identical; namespace drift cannot trigger reconstruction.
Only this separately proved ordinary-drive candidate is normalized to forward
slashes for the two returned SSH paths. No native prefix is stripped to invent
a transport alias, and no failed proof falls back to an ordinary path. The read
file primitive permits FILE_SHARE_READ only, denying write/delete sharing while
SSH uses either file. The store pins retained ancestry; actual read-root/file
security and parent binding remain native-authoritative.

Cleanup retires both read files before journal/root read capabilities, then the
actual namespace owner, then allows parent store journal/root cleanup. Each
close phase owns one directly retained release; partial native failure keeps
the exact capability. The namespace producer may itself take bounded phases.
It is never queried as current while still acquiring; its step owns that phase.
Actual namespace closure/drift permanently invalidates this projection. The
consumer must cancel its SSH child, retain process/projection/store owners,
and finish cleanup; no success/error string substitutes that cancellation.

## Evidence and consumer obligations

The source-authored native fixture requires existing genuinely generated key
and known-hosts records and actual protected roots. It covers both retained
targets, no publication/content changes, partial child close, parent close,
foreign actual store refusal, concurrent bound and safe generation reuse. Pure
role cases cover only production grammar. Service-context drift, retained
native failures, fork/PID namespace faults and actual SSH continuation remain
MANUAL_NOT_RUN procedures, without fake handles, namespace booleans or dummy
successes. No tests/builds/docgen/native execution occurred; no coverage or
latency claim is made. No private bytes enter logs, errors, SDN or snapshots.

A generic SSH facade must retain store, projection and its actual child-process
owner through terminal cleanup, call current paths before launch and each
continuation, and cancel on invalidation. It must not serialize owner fields.
Setup promising transport before generating secrets still needs a separate
actual service-context preflight; this existing-file projection proves no
authority over nonexistent files and does not change generic R2 preflight.
