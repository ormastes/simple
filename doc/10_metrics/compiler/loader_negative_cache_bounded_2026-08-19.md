# Loader negative-cache boundedness and invalidation evidence — 2026-08-19

## Scope

Pure-Simple interpreter module resolution and the compiler watcher's source
mutation bridge only. No `smf_mmap_native` or runtime C/Rust file was changed.
The workload is
`test/01_unit/compiler/interpreter/module_resolver_file_exists_spec.spl` in
interpreter mode.

## Correctness receipt

Final focused run:

```text
bin/simple test test/01_unit/compiler/interpreter/module_resolver_file_exists_spec.spl --mode=interpreter --fail-fast
8 examples, 0 failures
Duration: 692ms
```

The bounded examples prove that 300 distinct caller-sensitive misses retain at
most 256 combined cache entries and cause real eviction. Actual temporary-file
create, edit, move, and delete operations are routed through the production
watcher source-mutation bridge. Their exact receipt is five invalidated full
entries across four events/five path identities: create=1, edit=1, move=1,
delete=1, fast=0, precise-full=5, fail-closed-full=0, ambiguities=1.

A separate producer-spelling regression starts with one fast plus two full
entries. An edited path reported with a `./` spelling invalidates exactly one
fast entry and fail-closed clears exactly two full entries, with zero precise
matches and one normalization ambiguity. This proves an unrelated fast
invalidation cannot suppress the conservative clear.

`bin/simple check` passed for the resolver, source-mutation bridge, watcher
producer, and focused spec (4 files).

## Timing and RSS receipts

Command for both measured attempts:

```text
/usr/bin/time -v bin/simple test test/01_unit/compiler/interpreter/module_resolver_file_exists_spec.spl --mode=interpreter --fail-fast
```

| Attempt | Test state | Wall time | Max RSS | Interpretation |
|---|---:|---:|---:|---|
| Baseline | 5/5 pass | 2.12 s | 175,452 KiB | Diagnostic only |
| First post-change measurement | 6/7 pass | 1.79 s | 176,548 KiB | Diagnostic only; the failing assertion checked a mutation facade's unreliable boolean return after the mutation had completed, and was replaced by observable resolution-state assertions |
| Final correctness | 7/7 pass | 295 ms runner duration | not remeasured | The three-cycle guard prohibited another timed/RSS rerun |
| Producer/telemetry correctness | 8/8 pass | 692 ms runner duration | not measured | Third/final cycle; diagnostic Rust-seed correctness only, with no performance inference |

These timing/RSS rows are retained but **not admitted self-hosted evidence**.
The repository `bin/simple` symlink resolves to
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
and every invocation identified that executable as a Rust bootstrap seed. This
preserves the existing bug record's unblock condition: rerun the same command
once an admitted pure-Simple Stage-3/Stage-4 binary is deployed. The measured
RSS change (+1,096 KiB, +0.62%) is not a regression verdict because the
post-change measured attempt was not fully green and the executable is
inadmissible.

## Implementation bounds

- One 256-entry budget covers both caller-independent and caller-sensitive
  caches, including positive and negative results.
- FIFO eviction removes the result and its probe-dependency record together.
- File and directory probes are indexed only during uncached resolution; cache
  hits add no filesystem probes.
- Create/edit/delete invalidate exact and ancestor/descendant probe
  dependencies; move invalidates both old and new paths.
- Watcher added/modified/deleted events call the resolver owner after a real
  source mutation; the move bridge passes old and new identities atomically.
- Fast entries are conservatively invalidated on every mutation because their
  key omits the caller. Fast, precise-full, and fail-closed-full totals are
  independent. Any unmatched producer path increments normalization ambiguity
  telemetry and fails closed by clearing the remaining bounded full cache,
  regardless of how many fast or precise entries were already invalidated.
