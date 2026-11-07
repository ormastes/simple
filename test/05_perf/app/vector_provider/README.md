# Matched Simple DB and live HTTP benchmark

Uncompiled fixture implementation. No application/performance result is claimed.
The Python regression tests exercise synthetic record rejection and statistics
only; their output must never enter a performance cohort.

Build `db_scalar.spl`, `db_vector.spl`, `http_scalar.spl` and `http_vector.spl`
with the same qualified pure-Simple compiler/backend/runtime, source snapshot
and flags. Their sibling imports share all workload and validation logic.
Only vector adapters import concrete dynamic-provider construction.
The DB owner is carried in a record slot, matching the production
PureDatabase owner boundary for the tracked native Option<trait> limitation.

## Work and timing

DB uses actual PureDatabase, 1025 or 65536 rows and 32 queries per batch. Both
production query APIs cache the last exact SQL text per table in
`_PureDatabase/pure_database.spl` (`_select_cache_hit_v1`). The 32 successive
thresholds differ, including the boundary between batches, so neither lane
gets a result-cache shortcut. There is no direct cache mutation.

HTTP uses the actual server accepting-owner path, one persistent loopback
listener, and 128 fresh connections per batch. A synchronous client writes
the bounded complete request before accept/serve/read; this is a serial live
TCP workload, not a concurrency/throughput claim. The same arrangement runs
in both modes. Complete response bytes must match within and across lanes.

Every process constructs its DB/provider/listener once, performs three warmup
batches, then one measured batch. Setup, provider admission, result oracles,
output encoding and close are outside the measured interval. The parent
runner launches 30 development or 100 release pairs, alternating lane order;
fresh processes give equal initial state but include repeated setup cost in
the overall scheduling budget. RSS is whole-process/startup-inclusive, not
steady-state RSS. Do not substitute process wall time for the emitted batch
duration. Failed samples stop the cohort and retain partial evidence.

## Input manifest and invocation

`scripts/check/run-item5-matched-app-performance.py --manifest FILE --output
FRESH_DIRECTORY --samples 30` requires schema
`item5-matched-app-performance-v1`, mode `production`, exact 40-character
`app_source_commit`, `app_source_tree`, `producer_source_commit`,
`functional_app_source_commit`, local `source_repository`, decimal
`provider_id` and `implementation_id`, and `{path, sha256}` entries for
`db_scalar`, `db_vector`, `http_scalar`, `http_vector`, `provider`, `compiler`,
`runtime`, `watchdog`, `functional_evidence`. The latter must be a completed
canonical app runner's `evidence.env`; the runner checks all four successful
quiescent watchdog receipts, producer/runtime/provider identities and retained
Hello hash. It checks the actual Git objects prove identical production `src`
trees between functional and benchmark commits (test-only additions may differ).
Supply actual captured build identities; this runner
does not manufacture or certify producer lineage. Compiler/runtime/provider
inputs and all app files are rehashed after the cohort.
The runner copies the verified production DSO into its fresh output's
`build/providers/` directory and passes that relative path from the output
working directory. This preserves the loader's approved-root policy; both
the original and staged artifact are checked for drift.
Host CPU/kernel/governor/load metadata is captured before/after. Exact runner,
Python, Perl, nm, git and watchdog hashes are retained and checked for drift.

Default limits: one hour total, 1200 seconds/process, 1048576 KiB process-tree
RSS. All execution is sequential. Increasing a limit requires an explicit
runner argument; no automatic retries. The provider must be a production DSO
without test observer dependencies. Instrumented exact-ISA/call evidence is
a separate cohort and must bind the same workload/implementation. This runner
checks reported provider success counts, not independent hardware execution.

Output preserves each command/stdout/stderr/watchdog receipt, raw sample
records, nearest-rank p50/p95 and paired vector/scalar ratios. Successful output
is labeled `measurements-complete`, not release/ISA/bootstrap qualification.
Archive/producer admission, scalar no-load evidence, physical-target performance
and release acceptance remain separate gates.
