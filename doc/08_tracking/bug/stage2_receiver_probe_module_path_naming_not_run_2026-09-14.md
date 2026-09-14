# Stage 2 receiver probe intermittently reports `compiler.common.module_path_naming` as NOT_RUN

- **Filed:** 2026-09-14
- **Status:** OPEN — 2 failures in 3 runs, across two different trees
- **Severity:** blocks a bootstrap lane non-deterministically

## Symptom

The Stage 2 trust-root lane

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
   --mode=dynload --jobs=half --produce-stage3-receipt=verify-landed-compiler-fix
```

fails its receiver probe with

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
error: in-process native-build: build failed: 0 failed, 0 unverified, 1 not run,
       1 ok of 2 unit(s) — NOT_RUN: compiler.common.module_path_naming
```

and the lane exits 3: `--stop-after-stage2 requires a successful admitted Stage 2 compiler`.

Observed runs (F74 round 3, macOS arm64): run 1 `def2a9c30a1` FAIL, run 2
`def2a9c30a1` PASS, run 3 `4f4d0e12832` FAIL, run 4 `4f4d0e12832` PASS. Same
command, same host. Re-running is currently the only workaround.

## Mechanism — bookkeeping, not a scheduling race

`stage2-receiver.log` shows the build is **sequential**, which makes the
recorded reason ("never started (build ended first)",
`src/compiler/80.driver/driver_build/build_outcome.spl:257`) hard to take at
face value:

```
[build] phase=native_compile state=running ... done=0 total=2 ... current=compiler.common.module_path_naming
[NATIVE] codegen: 2 uncached module(s), concurrency=1 (build() compiles modules sequentially in this process)
find_llc: ... resolved=[/opt/homebrew/opt/llvm@18/bin/llc]
find_llc: ... resolved=[/opt/homebrew/opt/llvm@18/bin/llc]
===== build outcome summary =====
OK=1  ERROR=0  CRASHED=0  TERMINATED=0  TIMEOUT=0  NOT_RUN=1
  - compiler.common.module_path_naming
      reason: never started (build ended first)
```

`llc` is resolved **twice**, once per module, so both modules were processed —
yet one outcome is `OK` and the other defaults to `NOT_RUN`. With concurrency 1
and sequential compilation, a genuine "build ended first" race is unlikely. The
more probable defect is an **outcome that is never recorded**, leaving the unit
at its `NOT_RUN` default. The unit that loses its outcome is the one that was
`current` when `native_compile` began.

## Do not relax the probe

`0 failed, 1 not run` means the build did not run everything it planned. The
probe is correct to refuse it. The fix belongs in the outcome bookkeeping, not
in the gate. Not bisected; no repro smaller than the lane itself.
