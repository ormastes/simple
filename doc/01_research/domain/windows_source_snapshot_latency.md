# Reducing source snapshot cost

<!-- codex-research -->
Date: 2026-10-05. Status: research; alternatives are not implementation approval.

## Relevant external designs

Bazel separates action-result metadata from content-addressed files. This suggests
identifying reusable source bytes independently from the particular build request,
then identifying the action from its full inputs, compiler, runtime and options.
The cache documentation also identifies modification of inputs during a build as
a correctness hazard. Reuse must preserve the relationship between the bytes
hashed and the bytes consumed; a cheap timestamp check is not a replacement for
that relationship.

Source: [Bazel remote caching](https://bazel.build/versions/7.1.0/remote/caching?hl=en).

Ninja supports explicit and implicit dependencies and compiler-produced dependency
information. A Simple design can likewise retain discovered dependencies and
invalidate affected work instead of treating every source file as an input to
every action. Import resolution also depends on search paths, package manifests,
configuration, generated inputs and sometimes previously absent candidates; the
new design must model those dependencies rather than copy only the last list of
successfully imported files.

Source: [Ninja manual](https://ninja-build.org/manual.html).

Bazel's minimal-output approach avoids materializing data that an action does not
need. The transferable idea is separating a complete logical identity from eager
physical copies: materialize required immutable source blobs only. This is an
analogy, not evidence that Simple already supports lazy source materialization.

Source: [Bazel output service](https://blog.bazel.build/2024/07/23/remote-output-service.html).

Windows NTFS change journals record filesystem changes and provide a possible
platform-specific accelerator for dirty-file discovery. They do not supply an
atomic immutable source snapshot. Journal continuity, missing events, unsupported
filesystems, and concurrent changes need an explicit conservative fallback. Do
not require administrator configuration changes as a default build dependency.

Sources: [Microsoft change journal records](https://learn.microsoft.com/en-us/windows/win32/fileio/change-journal-records),
[Microsoft journal query API](https://learn.microsoft.com/en-us/windows/win32/api/winioctl/ni-winioctl-fsctl_query_usn_journal).

## Recommended direction for selection

Use a persistent dependency index plus content-addressed immutable file storage.
Validate changed inputs, build a dependency-scoped manifest, and share immutable
blobs across actions. Keep frontend identities backend-independent only where
semantic configuration is identical; backend objects need separate action keys.
Cache runtime objects and link inputs separately from source admission.

Start with portable dependency/content tracking. Add journal or watcher hints
only after the fallback and invalidation tests pass. Existing release qualification
may still require a complete repository identity, but that identity need not force
copying every source file for every one-module compilation.

Avoid hard links to mutable workspace files: writes through either name can
modify the purported snapshot. Copy immutable blobs once, or use an established
copy-on-write mechanism with verified semantics. Bound in-memory catalogs and
parallel hashing buffers; retain data by snapshot leases and reclaim unused blobs
without invalidating active consumers.

## Evidence required

Measure bytes read/copied, files enumerated/hashed, process launches, elapsed time,
cache hits and peak/retained memory for cold, unchanged warm, one-file edit,
dependency edit, unrelated edit, backend switch and malformed cache use cases.
The user's sub-100-ms compile target remains unproven. Snapshot acceleration alone
does not address the observed object-to-executable delay.
