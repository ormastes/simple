# FAT32 repeated positioned reads still revalidate the complete chain

## Status

Open. The safe 2026-08-22 change removes full-chain allocation from
`Fat32Filesystem.read_at`, but deliberately retains no cross-call cluster
cache. This preserves bounded memory and avoids stale traversal state across
separate opens, writes, remounts, and concurrent descriptor operations.

## Reproducer and structural evidence

Read a `C`-cluster FAT32 file in one-cluster positioned chunks at monotonically
increasing offsets. Fail-closed validation walks all `C` FAT entries before
each chunk copies bytes, so `C` chunks perform `C²` FAT-entry reads. For 8,192
clusters (4 MiB at 512 bytes/cluster), that is 67,108,864 FAT-entry reads versus
8,191 links for a generation-safe cursor: about 8,193x structural amplification.

Runtime timing and RSS evidence could not be collected in this worktree because
the admitted self-hosted `bin/release/<triple>/simple` executable is absent.
The Rust seed was not substituted and bootstrap was explicitly out of scope.

## Required safe fix

Introduce a filesystem/mount mutation generation owned by the FAT32 mount
owner, then attach a bounded `(object identity, generation, cluster index,
cluster)` cursor to the serialized descriptor owner. Invalidate or reject it
on every FAT/namespace mutation and remount. Acceptance must cover separate
opens of one file, failed and successful writes, unlink/reuse, remount, and a
reader/writer race. Retained state must remain O(1) per live file object; a full
cluster-chain array per open is not acceptable.

## Current mitigation

Each individual `read_at` validates the complete chain before copying and
retains only the clusters covered by the caller's byte range. The transient
memory is O(requested clusters), not O(file clusters) per open; ordinary
one-cluster launch reads retain one `u32`. It rejects FREE, BAD,
reserved/out-of-volume clusters, EOC-before-range, invalid geometry, I/O
failure, and fuel exhaustion without exposing bytes first. The snapshot also
prevents a concurrent FAT-link change from redirecting traversal after
validation, matching the prior whole-chain snapshot behavior. Positioned
writes reuse the one local chain already validated for allocation instead of
walking it twice.
