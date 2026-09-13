# Site 9: Stage 2's Stage-3 route allocates without bound in `native_compile` (killed at 124)

# Site 9: Stage 2's Stage-3 route now times out in `native_compile` (status 124)

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-8, `work/bootstrap-full-6-2026-09-12` at `272482747da`,
  run `build/bootstrap-boot8a` (08:11:19 -> 08:33:13, 22m, load ~23-35, `--jobs=10`).
- Severity: **the current `--stop-after-stage2` admission blocker**, and the successor to
  site 8 (`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`, CLOSED/FIXED).
- Candidate: `build/bootstrap-boot8a/stage2/aarch64-unknown-linux-gnu/simple`, sha256
  `95763bffee64a74ee9d7c876ec27b37dc798ed9bb403ec502a8e42660388ad74`, 152199352 B
  (executable pin: `scratchpad/boot8/pin/simple.boot8.stage2`, same sha).

## The verdict, verbatim

```
Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
| error: stage2 failed the positional pure-Simple Stage-3 route (status 124)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stage-2 sanity is green on this candidate: `status=pass`, `version_output=simple-bootstrap
1.0.1-beta.1`, `frontend_smoke_status=0`, `frontend_smoke_bootstrap0_raw_status=0`,
`frontend_smoke_bootstrap1_ran=true`, `frontend_smoke_bootstrap1_raw_status=0`,
`frontend_smoke_bootstrap_mode_status=0`, `sha_stable_status=0`, `checks_run=5`.
The receiver step, which is the umbrella that CONTAINS the route probe, reports
`status=fail`, `runtime_compare_status=0`, `probe_exit=1`.

## `124` is a timeout, and the limit is the gate's own 180 s

`scripts/check/check-bootstrap-stage2-struct-receiver.shs:124` sets
`stage2_route_timeout=${STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS:-180}` and invokes the candidate
under `timeout -k 5s "${stage2_route_timeout}s"` (`:151`). `124` is GNU `timeout`'s time-limit
exit, so the route did not fail — it was killed.

## Where it was killed, measured

`stage2-receiver.log`, last four lines:

```
[build] phase=native_cache state=running ... done=2 total=2 ... elapsed_ms=7146 current=complete
[build] phase=native_compile state=running unit_kind=modules done=0 total=2 remaining=2
        succeeded=0 cached=0 failed=0 task_done=5 task_total=6 elapsed_ms=7168 dt_ms=22
        current=compiler.common.module_path_naming
[NATIVE] codegen: 2 uncached module(s), concurrency=1
```

So the route completes `parse`, `hir`, `monomorphize`, `mir` and `native_cache` (2/2) in
**7.2 s**, enters `native_compile` on `compiler.common.module_path_naming`, and produces no
further progress line in the remaining ~173 s. Note the contrast with site 8's run, which
reached `native_compile` at `elapsed_ms=94426`: this candidate gets there 13x faster and then
stops emitting.

## Answered: neither slow nor hung — **divergent**

The replay was run (`scratchpad/boot8/probe9.sh`, same env and fixture as the gate, ceiling
raised 180 s -> 2400 s, pinned candidate `95763bffee64a74e...`). It reaches exactly the same
point — `native_cache` 2/2 at `elapsed_ms=7734`, then `native_compile` on
`compiler.common.module_path_naming`, then `[NATIVE] codegen: 2 uncached module(s),
concurrency=1` — and emits nothing further. The compiler process (pid 3170289, the child of
`timeout`) was sampled directly from `/proc`, 45 s apart:

| sample | utime (ticks) | stime | state | VmRSS |
|---|---|---|---|---|
| t0 | 8109 | 273 | R | 4 584 240 kB |
| s1 | 8417 | 279 | R | 4 754 708 kB |
| s2 | 11290 | 327 | R | 6 289 820 kB |
| s3 | 14486 | 457 | R | 8 972 872 kB |
| s4 | 17392 | 503 | R | 10 517 536 kB |
| final | 22118 | — | R | **12 963 184 kB** |

CPU is live (≈66 % of one core) so it is not deadlocked, **and RSS grows monotonically at about
1.9 GB per 45 s with no sign of converging** — 4.6 GB to 13.0 GB in roughly five minutes, for
TWO modules. Raising the timeout cannot fix this: the process would exhaust the host's 121 GB
rather than finish. It was killed by PID at 13 GB (`rc=143`) instead of being left to OOM a
shared box. **So `STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS` must NOT be raised** — the 180 s
ceiling is reporting a real unbounded-allocation defect in the pure-Simple native codegen path,
and the timeout is currently the only thing containing it.

## Next step for whoever picks this up

The allocating function is not yet named. `gdb -p <pid>` is **refused on this host**
(`ptrace_scope=1`; `ptrace: Inappropriate ioctl for device`, `No stack.` — the probe is
`setsid`'d and so is not a ptrace-eligible descendant). BOOT-7 got its stacks by launching the
candidate UNDER gdb rather than attaching (`scratchpad/boot7/gdb9.sh` + `trace9.py`); the
adapted harness for this lane is already in place at `scratchpad/boot8/gdb_site9.sh` +
`trace_boot8.py`, pointed at this candidate and this run's runtime authority. Run the probe
under gdb, let RSS climb to a few GB, interrupt, and walk the stack. That harness was written
for a SEGV (catch the signal, dump registers); site 9 needs a TIMED interrupt instead, and the
form that needs no python is
`gdb -batch -ex run -ex 'bt 30' --args <candidate> native-build …` with `kill -INT <inferior
pid>` from a second shell once RSS passes ~3 GB — gdb stops on the SIGINT and prints the stack — and, given site 8, check
first whether the allocation is another struct-copy shape: every `val` binding, field read and
argument of a struct type allocates, so a copy inside a hot loop over modules or symbols would
look exactly like this. See `dict_struct_key_identity_keyed_copied_key_misses_2026-09-13.md`.

## Localized 2026-09-13 on macOS: `BuildGraph.topological_order`

The "get a stack" step this record asks for was done on the macOS lane
(`aarch64-apple-darwin`, chain run 21,
`doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md`). macOS `sample` needs
no ptrace permission and no gdb harness:

```
sample <pid> 3 -file sample1.txt
```

**Every sample is SELF time in
`compiler__driver__driver_build__parallel__BuildGraph.topological_order`**
(`src/compiler/80.driver/driver_build/parallel.spl:274-305`) — 1751 + 100 + 55 +
50 + 41 + 40 + 35 + 24 + 13 + 12 + 11 + 11 + 9 + 2 + 1 samples spread across
offsets +292…+536, **with no callees recorded at all**. Nothing from
`driver_types.spl` or `mir_json.spl` appears, so this is not downstream of site 8.

Candidate: `.simple/storage/build/bootstrap-run21/stage2-rejected/aarch64-apple-darwin/simple`,
139,328,040 B, sha256 `e1ab37e7ba2caa3e587390c9d0d581b14ca4c93023e4cafe14abe28e5ee0c17f`
(mode 400 — copy out and `chmod +x` first). Route entered `native_compile` at
`elapsed_ms=3950`, `current=compiler.common.module_path_naming` — the same unit
this record names on Linux.

### The macOS RSS curve differs from the Linux one, and that matters

Re-running the probe unbounded and sampling RSS (`ps -o rss=`) at 240 s / 360 s /
480 s, with the route log checked at each point:

| t | RSS | route log |
|---|---|---|
| 240 s | 12.3 GB | `elapsed_ms=3579` |
| 360 s | 9.8 GB | `elapsed_ms=3579` |
| 480 s | 9.4 GB | `elapsed_ms=3579` |

Flat and then **falling** — not the monotonic ~1 GB/45 s growth measured on Linux.
So on macOS the process is no longer allocating; it is burning CPU inside
`topological_order` over a structure it has already built. Either the Linux
reading is an earlier phase of the same defect (allocate a huge graph, then spin
on it), or the two lanes are failing differently. Both readings are open.

Two candidate causes, neither verified:

1. **Non-terminating loop.** `while stack.?:` with `stack.pop().unwrap()`. If
   `pop()` does not shrink the array in this native build, the loop never ends.
   That function already carries a comment about a *different* seed-interpreter
   divergence at this exact statement. A tight loop with no callees fits the
   sample exactly, and fits the flat RSS.
2. **Quadratic-or-worse work over a very large graph.** `order = order.push(node)`
   and `stack = stack.push(...)` in the inner loop, plus a node being pushed once
   per in-edge before it is visited. Inlined array ops also show as self time with
   no callees, and this cause is what the 9-12 GB resident set predicts.

Discriminate by printing `self.units.keys().len()` and an iteration counter from
`topological_order`, or by checking whether `pop()` shrinks natively in a fixture
built by the run-21 candidate (which builds now that site 8 is fixed).

## What is NOT yet known

The replay was run (`scratchpad/boot8/probe9.sh`, same env and fixture as the gate, ceiling
raised 180 s -> 2400 s, pinned candidate `95763bffee64a74e...`). It reaches exactly the same
point — `native_cache` 2/2 at `elapsed_ms=7734`, then `native_compile` on
`compiler.common.module_path_naming`, then `[NATIVE] codegen: 2 uncached module(s),
concurrency=1` — and emits nothing further. The compiler process (pid 3170289, the child of
`timeout`) was sampled directly from `/proc`, 45 s apart:

| sample | utime (ticks) | stime | state | VmRSS |
|---|---|---|---|---|
| t0 | 8109 | 273 | R | 4 584 240 kB |
| s1 | 8417 | 279 | R | 4 754 708 kB |
| s2 | 11290 | 327 | R | 6 289 820 kB |
| s3 | 14486 | 457 | R | 8 972 872 kB |
| s4 | 17392 | 503 | R | 10 517 536 kB |
| final | 22118 | — | R | **12 963 184 kB** |

CPU is live (≈66 % of one core) so it is not deadlocked, **and RSS grows monotonically at about
1.9 GB per 45 s with no sign of converging** — 4.6 GB to 13.0 GB in roughly five minutes, for
TWO modules. Raising the timeout cannot fix this: the process would exhaust the host's 121 GB
rather than finish. It was killed by PID at 13 GB (`rc=143`) instead of being left to OOM a
shared box. **So `STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS` must NOT be raised** — the 180 s
ceiling is reporting a real unbounded-allocation defect in the pure-Simple native codegen path,
and the timeout is currently the only thing containing it.

## Next step for whoever picks this up

The allocating function is not yet named. `gdb -p <pid>` is **refused on this host**
(`ptrace_scope=1`; `ptrace: Inappropriate ioctl for device`, `No stack.` — the probe is
`setsid`'d and so is not a ptrace-eligible descendant). BOOT-7 got its stacks by launching the
candidate UNDER gdb rather than attaching (`scratchpad/boot7/gdb9.sh` + `trace9.py`); the
adapted harness for this lane is already in place at `scratchpad/boot8/gdb_site9.sh` +
`trace_boot8.py`, pointed at this candidate and this run's runtime authority. Run the probe
under gdb, let RSS climb to a few GB, interrupt, and walk the stack — and, given site 8, check
first whether the allocation is another struct-copy shape: every `val` binding, field read and
argument of a struct type allocates, so a copy inside a hot loop over modules or symbols would
look exactly like this. See `dict_struct_key_identity_keyed_copied_key_misses_2026-09-13.md`.

---

## MEASURED CAUSE (BOOT-9, 2026-09-13) — `BuildGraph.topological_order` never returns

Not inferred. The pinned candidate was launched UNDER gdb (`gdb -p` is refused
here; harness `scratchpad/boot9/gdb9.sh`, log `gdb9.log`, RSS series
`gdb9.rss`) on the gate's own fixture and env, and interrupted three times once
VmRSS passed 6 GB (6 037 772 kB, 8 847 448 kB, 8 689 316 kB). All three stacks
are IDENTICAL in frames and in depth — a runaway loop, not recursion:

```
#0  <hashbrown::map::HashMap<usize, ()>>::insert
#1  <std::collections::hash::set::HashSet<usize>>::insert
#2  simple_runtime::value::heap::register_heap_ptr
#3  <simple_runtime::value::core::RuntimeValue>::from_heap_ptr
#4  rt_tuple_new
#5  compiler__driver__driver_build__parallel__BuildGraph.topological_order
#6  compiler__driver__driver_build__parallel__ParallelBuilder.build
#7  compiler__driver__driver_aot_native_output__CompilerDriver._compile_to_native_with_backend_session
...
#12 main
```

The return address in frame 5 is `0x381b400`, the instruction after
`bl rt_tuple_new` at `0x381b3fc` — i.e. `stack = stack.push((node, true))`,
reached through `visited[node] = true` (`rt_index_set` at `0x381b3e8`). Every
allocated tuple is registered in the runtime's heap-pointer `HashSet`, which
only grows; that set, not the tuples, is what turns the loop into 1.9 GB per
45 s.

The loop's only exit is `rt_is_some` on the stack ARRAY:

```
381b350: mov  x0, x23
381b354: bl   3f10cbc <rt_is_some>
381b36c: b.ne 381b2a8            ; dead: rt_is_some(array) is always true
```

Source: `while stack.?:`. `.?` on a collection receiver lowers to `rt_is_some`,
which is true for any non-nil array including `[]`. Once the DFS drained, every
iteration popped nil, re-pushed `(nil, true)` and grew `order` — forever. Full
analysis, the cross-lane truth table and the census of the other
collection-receiver `.?` sites:
`dotq_on_empty_collection_reads_present_2026-09-13.md`.

**Lane-independent, so it is cheap to reproduce without a bootstrap.** The seed
`simple run` lane (sha256 `3d120a6f9ab5704b...`) on a 3-unit chain prints
`units=3` and never prints the order (killed at 150 s; probe
`scratchpad/boot9/probe/topo.spl`, RED log `scratchpad/boot9/red_topo.log`).
After the fix the same probe answers `ORDER=0,1,2,`.

## Fix

`src/compiler/80.driver/driver_build/parallel.spl:285` — `while stack.?:` ->
`while stack.len() > 0:`. Same DFS, same comparison, no design change. Spec
`test/01_unit/compiler/driver/build_graph_topological_order_terminates_spec.spl`
(RED `2 examples, 2 failures` -> GREEN `2 examples, 0 failures`). The
behavioural example re-reads the source and refuses to EXECUTE the loop if the
divergent spelling returns, so a regression fails loudly instead of hanging a
suite; the structural example is the assertion in that case.

The gate's `STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS` was NOT raised and must not
be: 180 s was reporting a real defect.

## Site 9 fixed; the same loop then exposed site 10 (2026-09-13, BOOT-9)

Run `build/bootstrap-boot9a` (09:06:58 -> 09:30:26, head `3fdf82ea1d2`) built a
new candidate `ac5a205d9030bea6...` (152198144 B) whose `topological_order`
carries no `rt_is_some` at all — the loop head is now a direct array-length
read (`ldr x8,[x21,#8]; cmp x8,#0; b.le exit` at `0x381b358`), so site 9's
dead exit branch is gone and the fix is proven IN the codegen that matters.

The route still exited `124`, and the classification run says it is the same
KIND of defect one step further in, not a slow build: VmRSS 40 MB -> 6.07 GB in
121 s (`scratchpad/boot9/gdb10.rss`), three interrupts again all naming
`BuildGraph.topological_order -> rt_tuple_new -> register_heap_ptr`. The cause
is `val (node, expanded) = stack.pop().unwrap()`: `rt_array_pop` returns the
element raw and `.unwrap()` lowers to `rt_enum_payload`, which nils a non-enum.
Measured in the exact Stage-2-compiling lane and directly in the candidate —
see `stage2_unwrap_on_array_pop_yields_nil_2026-09-13.md`. Fixed by reading the
top by index and truncating.

The ceiling was still not raised.
