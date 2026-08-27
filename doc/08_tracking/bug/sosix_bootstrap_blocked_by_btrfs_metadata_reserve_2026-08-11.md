# SOSIX bootstrap blocked by btrfs metadata reserve

**Date:** 2026-08-11  
**Status:** open; no compiler verdict

The final bounded, cache-preserving full-bootstrap attempt began after the
tracked Rust diff fingerprint stabilized. During input fingerprinting, its
`find src/compiler_rust ...` child stalled in `btrfs_tree_read_lock`.

The repository-mandated preflight reported:

```text
Device unallocated: 1.00MiB
Free (estimated): 275.49GiB
Metadata,DUP: Size:55.51GiB, Used:46.60GiB (83.95%)
```

The operational rule requires roughly 5 GiB device-unallocated space before a
bootstrap or evidence run. Estimated free space is not sufficient on this
btrfs layout. The attempt was terminated before accepting any build result.
No cleanup, balance, deletion, compiler publication, or QEMU run occurred.

Resume after an operator safely reclaims or migrates data and the mandatory
preflight is green. Recheck the tracked Rust input fingerprint, retain
`SIMPLE_NO_STUB_FALLBACK=1`, and use the hot bootstrap cache for one admitted
full deploy.
