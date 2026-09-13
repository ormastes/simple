# Site 9: Stage 2's Stage-3 route allocates without bound in `native_compile` (killed at 124)

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

## RESOLVED 2026-09-13 — and BOTH candidate causes above were wrong

Root cause: **`.?` on an empty array evaluates TRUE under native codegen**, so
the `while stack.?:` DFS loop in `topological_order` never terminated. Full
evidence, a 10-line standalone reproduction, and the blast radius are in
`native_codegen_dotq_true_on_empty_array_2026-09-13.md`. The compiler defect is
still OPEN; only this call site is routed around it (`while stack.len() > 0`).

Both causes this record proposed are disproven by instrumented output from a
Stage-2 candidate on the real graph:

- **Cause 1, "`pop()` does not shrink natively" — FALSE.** Every probe line
  reports `stack_after_pop` one less than `stack.len()` at the loop head. `pop()`
  shrinks correctly.
- **Cause 2, "quadratic-or-worse work over a very large graph" — FALSE, and the
  premise was wrong.** `units.keys().len()=2`, and both units report
  `deps.len()=0`. V=2, E=0. The correct walk is four iterations. No algorithmic
  property of any topological sort is reachable at that size, so the task-level
  plan to rewrite this to Kahn's algorithm was dropped: a Kahn loop written
  `while ready.?:` would have spun identically.

The route log's own `total=2` said this all along and was read as 886.

### Before / after, same fixture, same runtime authority

| | `native_compile` entry | outcome |
|---|---|---|
| before | `elapsed_ms=3747` | no further progress line; killed at 100 s / 180 s (status 124) |
| after | `elapsed_ms=3764` | `state=failed` at `elapsed_ms=3983` — **219 ms**, both units attempted |

The walk that never returned now returns, and the build reaches and reports on
every unit. Site 9 is closed.

### Site-8 verdict for macOS, which this unblocks

`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md` could not be
confirmed on macOS while this site was live, because `serialize_mir_function`
runs downstream of `topological_order` and was never reached (see the correction
appended to that record). With this fix the route runs MIR serialization and
reaches LLVM IR emission and `llc`: **no SEGV, `serialize_mir_function` absent,
status 1 not 139.** Main's `driver_types.spl` fix holds under aarch64 macOS
codegen. That verdict now rests on a route that actually executed the code path.

### Successor: site 10

The route still fails, on two NEW and unrelated defects, both downstream of
everything above and both in `native_compile` of the 2 units:

1. **`llc` rejects the emitted IR — duplicate local value name.**
   `AOT compile error in compiler.common.module_path_naming: llc failed (exit 1)`
   / `module.ll:109:3: error: multiple definition of local value named 'l14'` /
   `%l14 = getelementptr i8, ptr %l25, i64 0  ; copy`. The pure-Simple LLVM
   emitter reuses a local name within one function.
2. **Capsule identity computed over empty content.**
   `native-capsule-source-mutated:...stage2_module_path_naming:
   capsule-identity=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
   disk-identity=404569fc...`. `e3b0c442...b855` is the SHA-256 of the EMPTY
   string, so the capsule side hashed nothing and the mismatch is a false
   positive against a file that was never mutated.

Not fixed here.

### Divergence-delta escape record (required by `.claude/rules/vcs.md`)

PR #768 landed on a `check-test-tree-divergence-delta` PASS over a pre-existing
red. Verdict: `PASS — 3218 pre-existing offender(s), 0 introduced by this range`;
base verdict `FAIL — 3946 diverged vs 965 baselined (3084 new, 103
fixed-but-still-baselined); 32 mirror-only (31 unallowlisted, 0 stale-allowlist)`.
Offender list saved by the helper to
`/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T//test_tree_divergence_preexisting.txt`
(host-local temp; regenerate with
`sh scripts/check/check-test-tree-divergence-delta.shs <BASE> <NEW>`). The range
touches no mirror pair: its only test file is the new
`test/01_unit/compiler/driver/build_graph_topological_order_terminates_spec.spl`.

### Open risk, not closed by PR #768

No census was run for other `while <arr>.?:` / `if <arr>.?:` sites in the
bootstrap closure. Site 10 is therefore **not** provably the only remaining
obstacle to Stage-2 admission — another call site could hit the same `.?` defect.
That census belongs to the compiler-fix lane; until it exists, treat "site 10 is
the last blocker" as unverified.
