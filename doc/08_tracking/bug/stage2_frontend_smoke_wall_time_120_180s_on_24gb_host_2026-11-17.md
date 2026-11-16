# Stage 2 frontend smoke: 120–180 s wall time for p2_add on a 24 GB host (2026-11-17)

- **Status:** open (perf)
- **Severity:** P2. It blocks Stage 2 admission on small hosts at the default timeout.
- **Lane:** release/1.0.0. Stage 2 bootstrap on WSL Ubuntu-24.04 (23 GiB RAM, 2 GiB swap). The binary was pinned at `ca03d60c15a`.

## Symptom

`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2` rejected a correctly built Stage 2 compiler:

```
sanity FAIL - frontend smoke exited 124 (bootstrap-mode pass: 0)
bounded-log-error: timeout   (timeout_seconds=180)
```

The probe is `native-build --backend llvm --entry src/compiler/bootstrap_admission/p2_add.spl`, a one-function file. It runs under `COMPILER_BUILD_TIMEOUT_SECONDS` (default 180).

## Not a regression

I ran the build sequentially on the same host, with the same HOME, TMPDIR and `SIMPLE_RT_OBJ_CACHE_DIR` the sanity probe uses. Nothing else was running.

| binary | run 1 | run 2 |
|---|---|---|
| previously admitted p2 (2026-11-16 07:12) | 180 s | 132 s |
| rejected Stage 2 (`ca03d60c15a`) | 121 s | 131 s |

All four runs exited 0. The old binary admitted earlier only because it finished just inside the limit.

## Where the wall time goes

The build's own `elapsed_ms` counter reports about 19 s through link. The wall time outside that counter is the bug. Per-line timestamps from one run:

1. **About 37 s of startup** before the first `[cache-scope] published` line.
2. **About 10 s for each worker spawn.** HIR, MIR and the per-file worker each run as a child process: lines at 49 s, 61 s, 68 s, 78 s, 89 s and 96 s for a single module.
3. **The pool admits 0 workers on a 24 GB host.** It logs `[file-worker] WARNING: pool admits 0 worker(s) under the tree headroom ... degrading to 1`. The static worker estimate is 6.8–26 GB, while the measured peak commit is 0.86–1.3 GB.
4. **The cold runtime object cache compiles the runtime C serially.** This takes more than 200 s without a warm `SIMPLE_RT_OBJ_CACHE_DIR`. With a warm cache, link takes 4.5 s. All four timed runs above used a warm cache; the rejected bootstrap run (exit 124) is the one that went past 180 s.

All of this breaks the first-object-in-10 s rule. A one-function file should reach its first `.o` in seconds.

## Workaround

Run the bootstrap with `COMPILER_BUILD_TIMEOUT_SECONDS=600`. The sanity scrub preserves this knob.

WORKAROUND(stage2-smoke-wall): the bootstrap runner on this 24 GB WSL host (boot3.sh, outside the repo) sets the timeout to 600 s for the whole bootstrap. No repo default changes. Remove the workaround once items 1-4 are fixed.

## Fix direction

- Profile and cut the 37 s startup.
- Spawn workers once, or keep them warm.
- Size worker admission from the measured peak commit rather than the static estimate.
- Prime the runtime object cache once per lane, in parallel.
