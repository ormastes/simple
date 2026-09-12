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
