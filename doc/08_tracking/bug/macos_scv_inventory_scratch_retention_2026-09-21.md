# macOS SCV cold inventory scratch retention

Status: OPEN — source correction implemented; native correctness, memory, and
performance qualification remain blocked. Scope: `aarch64-apple-darwin` only.
Related: compiler TODO 319 and `stage3_macos_compile_peak_rss_2026-09-21.md`.

Cold admission reduced every source file to an event but did not reclaim its
canonicalization, hashing, and file-read scratch. Publication sorted and
searched the growing inventory for every create, making initial application
quadratic. Digest validation allocated one text value per hexadecimal byte.

The correction opens one transient scope per file, promotes only that event,
and ends the scope before appending to the retained array. Scope failures
propagate through Git event production. Unique creates into an empty inventory
validate and append once, then sort once with a bounded-memory heap sort.
Duplicate, delete, update, and invalid events retain the sequential path.
Already sorted inventories use a linear fast path. Digest validation reads
ASCII bytes. Public inventory APIs remain exposed through the original module;
pure records and reduction now live in `compile_source_inventory_core.spl`.

## macOS Phase 2 evidence

Compiler: admitted Astra Stage 2, SHA-256
`9aea8349b6fb411e46b325ecff70d2924173533d4c2e71d41e2619e9998c41a1`.
Base checkout: `20245f731db`. Required integration predecessors include
`531f948d0fe` (transient ownership boundary) and the `80cc02571d4` lineage
(ASCII split and HIR ownership corrections).

Three focused native compile cycles used the bare positional pure-Simple
`native-build` route and its admitted runtime archive. These were diagnostic
single-process compiles; the required jobs=8 full compiler gate was not run.

| Cycle | Elapsed | Maximum RSS | Outcome |
|---|---:|---:|---|
| 1 | 12.22 s | 1,105,330,176 bytes | HIR rejected the existing `std.io` lock import |
| 2 | 8.45 s | 874,053,632 bytes | HIR passed; MIR lowering exited 139 |
| 3 | 5.67 s | 421,707,776 bytes | Smaller pure closure passed HIR; MIR rejected unsupported operations |

Cycle 1's lock import now names its actual `std.nogc_sync_mut.io.file_ops`
provider. Cycle 3 reports existing array `remove`, SHA core `get`, builder
`to_text`, binary inspector `bytes`, range-index, non-array iteration, and
inferred-enum lowering failures. It produced no executable. The final measured
compile peak is below 1 GB, but different closures and early failures mean
these rows are not before/after performance evidence for cold admission.

Logs remain under `build/native_probe/scv-inventory-memory/` in the isolated
worktree. The third run enabled `SIMPLE_NO_STUB_FALLBACK=1`.

## Remaining acceptance

The native fixture authors 256 repeated event scopes with digest/lifetime
checks, nested-scope refusal, a 2,048-entry reversed batch, and duplicate
generation checks. Its `--baseline` mode retains unscoped per-file work for
a comparable elapsed-time/RSS measurement. Neither mode executed because no
binary was produced. SSpec cases are also authored but unexecuted.

Fix the Phase 2 MIR blockers, run the fixture and matching baseline, then
qualify a full jobs=8 cold admission and compiler build below 1,000,000,000
bytes without a meaningful elapsed-time regression. TODO 319 remains open.
The three-cycle cap was reached; no further compile attempts were made.
