# Bootstrap outer RSS observation aborts on an exiting zombie stat

Status: observed; canonical guard source unchanged; no acceptance PASS.

The optional session outer wrapper process-tree-rss-watchdog.pl stopped the
owned imported-owner bootstrap after 2495 samples. Receipt status is
rss-measurement-failed, exit89, peak3528116KiB, quiescent1; it was not an RSS
limit breach. Its failure identifies malformed `/proc/1356878/stat`. The
retained prefix decodes to a timeout zombie with `Z 0 -1 -1`, so the process
has negative process-group/session values during exit. This is a process
observation edge case; do not silently disable canonical compiler guards.
Evidence: `build/native_probe/imported-owner-bootstrap/bootstrap.log` and
`process.env` in the owned `simple-items247-import-eq-20261020` worktree.

A kernel systemd scope with MemoryMax32GiB, MemorySwapMax0 and RuntimeMax3600s
was successfully created as an alternative to the extra outer sampler. The
canonical bootstrap and all its built-in guard behavior were unchanged. That
attempt stopped before Cargo because the disk floor was violated (19GiB<20).
Its log is `bootstrap-kernel-scope.log`. Both attempts are terminal, cached
seed/runtime outputs were preserved, and no Stage2 producer was admitted for
the imported-owner repair. Resume only when disk preflight can pass, using the
same owned cache; capture the kernel scope properties on a live retry.
