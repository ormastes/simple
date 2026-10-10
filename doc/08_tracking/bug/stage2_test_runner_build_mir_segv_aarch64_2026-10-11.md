# Stage-2 compiler SIGSEGV in MIR lowering of test_runner native-build (aarch64 Linux, 2026-10-11)

- **Filed:** 2026-10-11 (beta-release qualification lane)
- **Status:** OPEN (P0 — blocks the strict bootstrap Stage-2 compiler-test matrix
  and therefore the Stage 3→4 receipt chain on aarch64 Linux)
- **Host:** aarch64-linux (20-core, 121 GB), backend=cranelift, mode one-binary,
  `--runtime-bundle core-c-bootstrap`, stage-2-admitted compiler

## Symptom

`bootstrap-phase-verification --phase=stage2` task `test_runner_build` (and the
same command standalone) dies:

```
error: native-build worker terminated with signal 11 before producing a binary; NOT a compile failure.
  A SIGSEGV/SIGABRT is a crash in the compiler itself; take a backtrace from the core (see /var/crash).
```

Reproduced 4/4 times on 2026-10-10/11 (two in-lane matrix runs, one standalone
`run-linux-phase2-tests.shs`, one direct gdb-instrumented run). Crash point
varies slightly (HIR→MIR boundary; final visible phase always `mir`,
`lower_to_mir`), immediately after a cluster of `[mir-lower] WARNING: struct/class
name ... re-registered with a DIFFERENT field list ... bare-name field-index
lookups for this type are ambiguous across modules` warnings for test_runner
structs (`TestRecord`, `CounterRecord`, `TimingSummary`, `TimingRun`,
`CompileError`, `ChangeEvent`, `CostEstimate`).

Watchdog receipts show `status=complete exit_status=139` with peak RSS well
under the cap (4.8 GB vs 6.8 GB) — a genuine memory-safety crash, not a
resource kill.

## Minimal reproduction

```
env SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
  SIMPLE_RUNTIME_PATH=<phase2-runtime-capsule dir> \
  <stage2-admitted>/simple native-build src/app/test_runner_new/main.spl \
  --backend=cranelift --low-memory --threads 2 -o /tmp/simple_test_runner
```

from the repo root (~6 min to crash under host load).

## Evidence

- /tmp/beta-qual-evidence/segv-repro.log and segv-repro2.log (full stderr)
- Watchdog receipts: peak 4.8 GB < cap; exit_status=139
- /var/crash/ contains 2026-10-03 `compiler.snapshot ... stage2-compiler-tests
  ... .crash` files from an earlier session on this host — this defect
  predates the 2026-10-10/11 qualification lane.

## Not the (fixed) 2026-10-04 shard-worker SEGV

doc/08_tracking/bug/stage2_x86_64_hir_shard_worker_segv_startup_2026-10-04.md
was `request.binding` deref at shard-worker startup (x86_64), fixed by
01c7e678a79. This crash is aarch64, in the main build's MIR lowering, after
mir-lower struct re-registration warnings — a different fault.

## Suspected root-cause area (not confirmed)

Bare-name struct re-registration collisions during MIR lowering of the
test_runner closure: two modules register the same struct name with different
field lists; the "keeping EXISTING" policy leaves later modules' field-index
lookups addressing the FIRST registration's layout — an out-of-range field
index or stale layout pointer in MIR lowering would SIGSEGV exactly like this.
A confirmed backtrace needs a core from the crashing worker (the compiler's
own SIGSEGV handler intercepts in-process; gdb on the parent misses the
spawned worker — use `set follow-fork-mode child` or enable worker cores).

## Impact

- Strict bootstrap cannot complete: Stage-2 compiler-test matrix FAILs on
  `test_runner_build`, the bootstrap refuses Stage 3 resume ("do NOT resume
  Stage 3 from this output until the failure above is understood").
- Stage 2 build itself, sanity, and the planner admission receipt all PASS
  (see QUALIFICATION_FINAL.md); this defect starts at the test matrix.
