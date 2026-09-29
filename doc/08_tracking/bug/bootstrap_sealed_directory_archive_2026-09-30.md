# Frozen bootstrap authority cannot move across Linux parents

## Observed failure

Linux cached facet retry cycle2 reached preflight, then failed before compilation:
`mv stage2-runtime-authority attempts/attempt-20260929T133429-626718/stage2-runtime-authority: Permission denied`.
The authority directory belonged to UID1000 with mode0500. Its parent and the
destination parent were owned and writable, the ext4 mount was writable, and
no immutable attribute was present. Linux requires directory write permission
when a rename changes its `..` entry. The existing archive-loop comment that
only the parent needed write permission was incorrect for this case.

The canonical failure trap froze the partially populated attempt. Six stale
sanity leaves had separately been preserved before the failure. None may be
discarded or rewritten to obtain a clean retry.

## Production correction

`bootstrap_cache_archive_prior` retains ordinary file archival into the attempt.
For directories, `bootstrap_cache_archive_directory` renames the old directory
beside itself as `NAME.prior-attempt-ID`. It does not chmod, copy, or remove the
frozen directory. The attempt records the original and retained basenames in
`attempt-directories.tsv`. Names, canonical paths, attempt shape, symlinks,
collisions and finalized receipts are checked before mutation. Partial writable
or symlink-containing prior directories are refused immediately, before any
mapping or expensive rebuild; they cannot be promoted to frozen authority by
this helper.

Mapping intent is published before rename. An interrupted or refused rename
therefore retains both the original evidence and the intended destination;
attempt freezing refuses an incomplete mapping instead of admitting it.

`bootstrap_cache_freeze_attempt` validates the mapping and requires the retained
tree to be sealed and free of symlinks. It includes each mapped file in
`attempt-files.sha256` using a validated `../../NAME.prior-attempt-ID/...` path.
Existing `sha256sum -c attempt-files.sha256` consumers run from the attempt
directory and thus validate both local evidence and the retained directory.
No bootstrap admission consumer may treat a historical mapping as current
runtime authority. The current authority paths and cache keys are unchanged.

## Focused verification

The new shell regression invokes the actual production helpers as an ordinary
Linux user with mode0500 authority/admitted directories and mode0400 files.
It covers preserved inode/permissions/contents, ordinary files, mappings and
receipt checking, collisions, symlinks, finalized attempts and tampering.
The test retains its private fixture and does not invoke a compiler.

Actual run: Ubuntu 22.04 UID1000, exit 0. Retained fixture:
`/mnt/simple-bootstrap-6b2/sealed-archive-production-helper-test-20260930/archive.YNQqhy`.
The production-helper regression passed once, including tampered mapped-file
receipt rejection. Log SHA256:
`894e7babd3e4aa9b472d608bccacab728935605e6e821fcff32c80adb769e5ea`.

Operational cycle 3 already uses a separately recorded same-parent preservation
of the old authority. Its actual Stage2 compiler reused 1065 modules and
compiled 3 with zero failures, then linked in 55.2 seconds total. That run uses
the prior frozen source, not this production change. Its sanity/admission is
a separate gate; these counters are not a full bootstrap qualification.
