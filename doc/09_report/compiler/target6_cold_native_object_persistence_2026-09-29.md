# Target 6 cold native object persistence bridge (2026-09-29)

Status: the cold HIR receipts and accepted module-to-object paths can now be
converted to real, content-addressed native objects. The production driver
does not call this bridge yet; V3 graph publication, warm replay, and the
paired production time/RSS gate remain open.

`cold_hir_native_objects_persist_v1` requires one path per typed HIR receipt,
rejects missing or duplicate modules, reads each object through the bounded
regular-file no-follow byte reader, verifies ELF/Mach-O/COFF magic, and checks
the object digest, size, and path against its capsule receipt. It publishes
the actual bytes through the existing binary object CAS, whose put operation
checks staged bytes and published readback. The returned list retains only
module identity, object digest/size/format, capsule identity, and receipt
digest. It does not retain object byte arrays across modules.

Focused no-stub native evidence in the isolated Target 6 worktree:

- The Stage-2 pure-Simple compiler built the probe with 296 source units,
  zero failures, and a 220 KB linked executable.
- The probe exited 0 with `PASS cold_hir_native_object_persistence_probe`.
  It wrote a real 8-byte ELF fixture, checked its CAS readback by length and
  SHA-256, and rejected a tampered capsule digest and an extra module path.
- The CAS blob on disk had the expected SHA-256
  `04d8e7f584b75f7f8283cef817093ae335a973a28faf44284edb0e0ef9776432`.

The first probe used native `[u8]` array inequality for readback and failed
despite matching on-disk bytes; the corrected probe uses length plus SHA-256.
That observation is limited to this diagnostic Stage-2/native pair and does
not establish a general array-equality defect. The optimizer app could not
run through this Stage-2 binary (`unknown command 'run'`). No before/after
latency or RSS cohort was taken, so this is not a performance qualification.

Next production step: bind the accepted capsule identity to each path in the
driver, call this bridge after all cold native objects are accepted, attach
the resulting object digests to complete action/archive receipts, publish the
scoped V3 graph after archive readback, then prove warm linking and paired
cold/warm p95 time and peak RSS on the same fixture.
