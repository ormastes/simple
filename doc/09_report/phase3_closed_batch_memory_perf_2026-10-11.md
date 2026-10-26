# Phase 3 closed-batch memory and performance review

Status: observation only. No source optimization, compiler rebuild, cache
identity change, or performance improvement is claimed. Active and later runs
are outside this report's scope.

## Evidence and measurements

Reviewed `build/native_probe/phase3-original1220-80030-20261010/`:
`chunk07a-run/results.json`, `chunk08a-run/results.json`, their retained
diagnostics, and the corresponding `chunk07a`/`chunk08a` HIR terminal ledgers.
Producer: `b580919372e209ea2a10e6d8e919b0f90c5dc3100e76f958f584c5db0ace4778`.
Each result retains its separate source commit and request identity.

The 80 result rows have nearest-rank inclusive elapsed p50 **235.930 s** and
p95 **291.604 s**. These describe heterogeneous concurrent failed compiles;
they are not repeated-fixture benchmark percentiles or compiler CPU time.
Maximum recorded process-tree peak RSS is **910,300 KiB** for chunk08a
module-0684, below these requests' **1,048,576 KiB** per-worker limit.
This does not establish absence of leaks, combined batch peak RSS, or limits
for later attempts. Recognized streams total **617,425 bytes**.

Local machine-readable analysis is retained at
`build/native_probe/phase3-memory-perf-review-20261011/closed-batch-summary.json`
and `repeated-source-sample.json`. They contain task rows and extracted terminal
receipts, permitting independent recount without running a compiler.

## Attribution

The slow module-1202 example reports `claimed=116`, seven failed modules,
and `HIR aggregate failure`. Its `truncated workaround Git status output`
warning precedes compilation but is not evidence that workaround refresh
caused the compile failure or elapsed time. The warning's owner,
`src/app/bug/workaround_store.spl`, and its coordinator caller are already
dirty and owned by other work. No overlapping edit was made.

Across the on-disk per-task cache directories there are 82 queue directories
and 12,723 terminal receipts: 7,944 `PASS/CACHE_STORED`, 278
`FAILED/UNCACHED`, and 4,501 `BLOCKED/UNCACHED`. There are more queue directories
than task rows; these totals describe retained queue inventory, not an asserted
one-to-one attribution of all queues to the 80 latest launches.

The successful cache receipts cover 341 source paths, but **zero identical
source-path/terminal-key pairs**. A sampled dependency,
`src/compiler/00.common/dynamic_identity/closure.spl`, has 82 receipts and
identical captured source-byte SHA-256
`68e19e6fd9a95a5927d4274ad4fa83005b86ee18e93f02438568749a1e48d0f2`.
This is evidence of repeated source presence, not safe HIR reuse or a measured
number of redundant source reads/parses.

Current source linkage explains why byte equality is insufficient:
`driver_hir_cache.spl:80` hashes all frozen surfaces' canonical paths,
content hashes/lengths, module names and logical names. Its key function at
line 101 additionally binds source bytes, entry role, environment switches and
codec header. `driver_hir_recovery.spl:1` explicitly makes terminal PASS a
lowering outcome rather than cache-load authority. Different snapshot roots or
closures may intentionally specialize the result. This source inspection is
not proof that the current checkout is the exact producer implementation.

## Bounded follow-up and prevention checks

No actionable allocation cause or avoidable parse/read count is established
by these logs. Do not weaken closure keys, turn off correctness checks, share
per-entry HIR solely by file bytes, or suppress unresolved-symbol errors.

Use the next already-authorized bounded attempt to retain separate counters
for source reads/bytes, parse hits/misses, HIR hits/misses and phase durations
if its existing instrumentation supports them. Any new instrumentation must
first be bound to its own producer and reviewed outside active frozen inputs.
Only then select a source change. Required candidate checks are:

- Equal source bytes with changed imports, aliases, target, entry role or
  aspects still invalidate the appropriate semantic cache.
- Equivalent parse inputs under different capture roots reuse only an
  artifact whose path/provenance contract permits it; diagnostics retain the
  correct requested source location.
- Missing exports, recursive layouts and failed workers remain failures.
- A fixed fixture and immutable producer pair record p50/p95 elapsed time
  and peak/steady RSS, separately from batch inclusive scheduling time.

These prospective checks are **UNRUN**, not a verification PASS. Existing
tracking remains relevant:
`doc/08_tracking/bug/phase3_hir_import_materialization_time_rss_2026-08-22.md`,
`phase3_reexport_diagnostic_amplification_2026-10-10.md`, and
`parallel_build_workaround_index_lock_contention_20261008.md`.
