# Cold inventory replay allocation and sorting fix

The reported FreeBSD Stage 3 cold inventory covers roughly 16k source events and
previously consumed 2h50m and 26.3 GiB RSS before failing publication. Those are
historical incident observations, not measurements of this patch.

The old publication loop fed each event into the whole inventory: two insertion
sorts and one linear identity scan per create, plus successively larger snapshot
arrays. Cold replay now indexes identities and calls the same event authority on
zero or one entry. It preserves operation validation order, first-error reason,
no-op behavior, facet comparisons, and one generation increment per effective
event. Deleted slots are inactive and reused on recreation. Nonempty incremental
publication still uses the existing sequential path.

Canonical ordering uses stable bottom-up merge sort with one scratch array and
an already-ordered early return. Format and digests are unchanged. Stability
preserves the preexisting first-equal-entry behavior even for malformed duplicate
input outside the cold path.

## Structural bounds

For E events and U distinct admitted identities, cold replay requires O(E)
expected dictionary probes, O(U log U) final comparisons, and O(U) retained
entries/index/active flags/scratch. It creates only constant-sized intermediate
inventories per event. These bounds assume ordinary dictionary and array runtime
operations; they are not native allocation/RSS measurements. Digests-only input
events remain O(E). Historical file-reading and publication failures are separate.

## Regression gates and target evidence

- `test/01_unit/lib/scv/compile_source_inventory_cold_spec.spl` compares exact
  canonical bytes and generations against sequential replay through duplicate
  creates, modifications, comment-only changes, deletes, recreation, and no-ops;
  it pins first-error reasons and stable ordering on odd-sized duplicate input.
- `test/05_perf/scv/cold_inventory_workload.spl` replays 16,384 distinct events,
  asserts every resulting row is strictly ordered, checks all content digests,
  generation, count, and a byte-count checksum. It contains no file contents and
  excludes content hashing so replay allocations are observable.
- `test/05_perf/scv/cold_inventory_profile.shs /absolute/self-hosted/simple`
  runs that workload with GNU time and timeout, enforcing a 90-second whole-run
  budget and reciprocal 512-MiB maximum RSS budget. Budgets may be overridden
  with `SCV_COLD_MAX_SECONDS`/`SCV_COLD_MAX_RSS_KIB`; record overrides in evidence.
  Reports go to `SCV_COLD_REPORT_DIR` (default `build/scv-cold-profile`). Startup,
  parsing, preparation, replay and assertions are included. This Linux harness
  requires GNU time/timeout; FreeBSD target profiling must use its own admitted
  runner and equivalent wall/RSS limits.

Local validation: shell syntax and diff whitespace checks pass. No admitted
self-hosted runtime was available in this worktree. Simple tests, native wall
latency, and target RSS remain pending the parent lane's FreeBSD Stage 2 runner;
no speedup or memory reduction is claimed from structural bounds alone.
