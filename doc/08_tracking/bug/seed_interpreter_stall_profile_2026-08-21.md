# Seed interpreter stall — poor-man's profile (2026-08-21)

## Status
PARTIALLY RESOLVED — 01a3fa7e90d added level-gated stall counters (profiling only, no behavior fix); root cause subsequently addressed by e73a0bec647 (CowEnv). OPEN: confirm the profiled stall fully clears against these counters on a fresh run.


## Status
Profiled. **No fix landed** — no single defect was isolated with enough
confidence to change hot-path semantics. Level-gated counters added so the
next pass starts with numbers instead of guesses.

## Sampling method (what works on this host)
`ptrace_scope=1` and locked-down `perf` make `gdb -p <live pid>` impossible
(confirmed once: `Could not attach to process ... ptrace: Inappropriate ioctl`).
Working method — run the target as a gdb CHILD in batch mode and interrupt it
from a side shell:

    gdb -q -batch -x cmds.gdb --args /mnt/data/seedperf/simple.v2 lint <file>
    # cmds.gdb: run, then N x { echo ===SAMPLE===, thread apply all bt 40, continue }
    # side shell: sleep N; loop { kill -INT $(pgrep -P <gdbpid>); sleep <interval> }

Notes that cost time and should not be re-learned:
* `bt` alone is useless — the main thread only `pthread_join`s; all interpreter
  work is on **thread 2** (a big-stack spawned thread). Use `thread apply all`.
* Local-variable inspection is unavailable (frames print as `fn ()`), so
  `p obj_name` style evidence cannot be had; a gdb command-file error aborts the
  whole batch run.
* Do not `pkill -f <script>` from a Bash tool call — the pattern matches the
  wrapper shell and kills the caller.

## Top frames — `lint src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
9 samples, thread 2, leaf (`#0`) frames:

| leaf | samples |
|---|---|
| `Value::clone` <- `Vec<Value>::clone` <- `Arc::make_mut` <- `handle_method_call_with_self_update_inner` | 2 |
| `Vec<Value>::clone` <- `Arc::make_mut` <- same | 1 |
| `arg_binding::copy_value_type_in_place` <- `bind_args_with_values` | 2 |
| `__memcpy_avx_unaligned_erms` <- `_mi_heap_realloc_zero` (array grow) | 1 |
| `mi_heap_malloc_aligned_at` <- `evaluate_call` | 1 |
| `arcinner_layout_for_value_layout` (Arc alloc) | 1 |
| other | 1 |

Frame census (all frames, 9 samples): `exec_node` 37,
`handle_method_call_with_self_update{,_inner}` 53, `execute_function_body` 23,
`exec_block_fn` 23, `with_effect_context` 20, `evaluate_call` 20.

So ~45% of leaf samples are **array copy-on-write** in the identifier-receiver
array mutation path (`interpreter_helpers/patterns.rs:955`), and ~22% is the
value-type argument copy added 2026-08-21
(`interpreter_call/core/arg_binding.rs:24`).

## Top frames — `lint test/fixtures/perf/nested_if_240.spl` (484 lines, ~40 s)
10 samples. **Completely diffuse — no dominant leaf**: one sample each in
`CowEnv::is_local` (under `publish_live_bound_globals`), mimalloc free-list
refill, `copy_value_type_in_place` x3, `CowEnv::get`, `CowEnv::shared_contains`
(under `CowEnv::remove`), `restore_block_scope_shadows`. Frame census is
interpreter dispatch machinery (`exec_node` 49, `execute_function_body` 30,
`handle_method_call_with_self_update{,_inner}` 56).

The nested-if superlinearity is therefore **not** the array-COW hotspot; it is
per-call interpreter overhead multiplied by recursion depth.

## Counter evidence (new, level-gated)
`SIMPLE_PERF_COUNTERS=1` (+ optional `SIMPLE_PERF_COUNTERS_OUT=<path>`), on
`lint test/fixtures/perf/nested_if_240.spl`:

    VT_CALLS                     35889
    VT_ARRAY_ELEMS_SCANNED        1471
    VT_ARRAY_CLONES                  0
    VT_ARRAY_ELEMS_CLONED            0
    VT_OBJECT_FIELD_CLONES           1
    ARR_MUT_CALLS                 2011
    ARR_MUT_COW_CLONES               0
    ARR_MUT_COW_ELEMS_CLONED         0

i.e. on the small fixture neither suspect fires. The same counters have NOT yet
been read on the 4831-line file — see "blocked" below.

## Why the array COW clone is probably NOT a defect
`CowEnv::get_mut` (`compiler/src/value.rs:424`) promotes a name out of the
shared immutable `base: Arc<HashMap<..>>` into the overlay by CLONING the
`Value`. The base keeps its own `Arc` to the array forever (it is shared with
every other env built from the same template), so `Arc::make_mut` at
`patterns.rs:955` sees `strong_count == 2` and deep-copies the `Vec` on the
first mutation after every env rebuild. That copy is **required** by value
semantics — other envs sharing the base must not observe the mutation. The cost
is inherent to per-call env rebuild + COW promotion, not a missed fast path.

## RSS trend of the live worker (pid 3627470)
`/proc/<pid>/status` every 30 s for 3 min (allowed without ptrace;
`/proc/<pid>/stack` is NOT — permission denied):
4657836 -> 4626968 -> 4604192 -> 4624112 -> 4545924 -> 4559076 -> 4558420 kB,
`VmPeak` pinned at 6674172 kB throughout. **Flat/slightly declining — steady
working set, not a leak.**

## Blocked
The in-tree seed built from `src/compiler_rust` cannot lint the current working
tree: it dies at 7.7 s with
`error: semantic: nil is forbidden by the non-optional return contract of
'_parse_duplicate_typed_arg_signature'` — a pre-existing breakage from another
session's uncommitted `.spl` edits, unrelated to this work. `/mnt/data/seedperf`
is a separate experimental tree (`seedperf_on_*.patch`, `simple.v2/v3/v4`), so
its binary and the in-tree build are NOT the same compiler; timings must not be
compared across them. Re-run the counters on the big file once the tree lints.

## Baseline numbers (binary: /mnt/data/seedperf/simple.v2, shared loaded box)
`lint test/fixtures/perf/nested_if_240.spl`: rc=0 wall=39.46 s rss=703576 KB;
second run rc=0 wall=44.12 s rss=666740 KB.
