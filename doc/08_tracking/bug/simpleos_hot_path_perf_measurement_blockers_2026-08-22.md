# SimpleOS hot-path performance and memory blockers (2026-08-22)

Status: open; measurement blocked by missing admitted Stage-4 `bin/simple`.

The Rust seed is bootstrap-only and must not be used as a substitute runtime.
Consequently the required optimizer invocation and identical before/after
Simple timing/RSS measurements cannot currently run in this worktree.

## PERF-SIMPLEOS-001 — repeated simplebox admission work

The image builder validates the same admitted artifact in load, build, staging,
and package-policy paths. At the 256 MiB limit this performs at least three
full SHA-256 passes (at least 768 MiB of input traffic) plus repeated executable
parses. Hoist one immutable builder-owned validation decision and preserve the
existing receipt/admission checks.

## PERF-SIMPLEOS-002 — per-byte duplicate process capture

RV64 stdout currently takes the local capture mutex for every byte, appends to
the 4 KiB local prefix, then takes the scheduler observation mutex per byte up
to its 64 KiB bound. A full run therefore performs up to 65,536 scheduler lock
cycles while retaining both local and canonical copies; the 256-slot scheduler
can retain approximately 32 MiB across independent 64 KiB stdout/stderr bounds.
Add bounded batch append or make scheduler evidence the canonical capture owner.

Implemented structurally on 2026-08-22: the RV64 capture owner forwards fixed
256-byte batches and seals/flushes the ordered tail before scheduler exit.  For
`N` retained bytes, scheduler observation commits fall from `N` to
`ceil(N / 256)` (4,097 bytes: 4,097 -> 17; 65,536 bytes: 65,536 -> 256).
Capture locking and serial dispatch remain byte-oriented.  Logical retained
stdout storage does **not** decrease: the 65,536-byte canonical scheduler
prefix and 4,096-byte compatibility prefix remain, and the fixed pending batch
raises the bound from 69,632 to 69,888 bytes (+256 bytes, 0.37%), excluding
headers/capacity.  A value-parameter boundary may transiently copy another 256
bytes; allocator/COW behavior is unmeasured.  Keep this bug open until the
required admitted-runtime timing/RSS/optimizer evidence below is retained.

## PERF-SIMPLEOS-003 — repeated launch/stack byte materialization

Launch validation materializes each string twice and performs separate NUL,
length, and copy passes. Stack construction converts each argv/env string in
both layout and serialization passes, while by-value byte-buffer append helpers
may copy the growing frame repeatedly. Precompute owned byte vectors once and
serialize into one exact-sized mutable buffer. Preserve all existing 64 argv,
128 envp, 4,096-byte string, and 65,536-byte aggregate boundary tests.

## PERF-SIMPLEOS-004 — repeated fw_cfg directory scans

Each of four compiler-filesystem metadata reads buffers and scans the complete
fw_cfg directory independently. At 4,096 entries this is up to 1,048,592 MMIO
directory-byte reads plus four allocations/scans. Read the directory once and
resolve the closed four-name set in one pass before bounded payload reads.

## Required retained evidence

When an admitted Stage-4 runtime exists, run the optimizer once on every
touched `.spl` file and compare identical origin/candidate fixtures (same input
hashes), with 20 warmups and at least 10 samples. Retain p50, p95, maximum, and
`/usr/bin/time` peak RSS for:

- 256 MiB simplebox image staging;
- 64 KiB RV64 stdout capture;
- a near-64 KiB 64-argv/128-envp initial stack;
- a 4,096-entry fw_cfg directory resolving four metadata files.

Do not close these bugs from structural checks alone.
