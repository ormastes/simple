# Stage 3 bootstrap failure — measured on origin/main 3b676a17736 (2026-08-25)

Worktree: /mnt/data/worktrees/lane-boot-s5 (fresh, `git status --porcelain` = only my 2 untracked helper files)
HEAD: 3b676a17736bcd9d7be2289e41ef1fab9e8b7251 (unchanged before and after Stage 2)

## Seed
`cargo build --release --bin simple` -> SEED_RC=0 (4m58s). Script rebuilds its own
hermetic authority seed anyway; that build also finished clean.

## Stage 2 — HEALTHY
Command: `--strategy=adhoc --full-bootstrap --stop-after-stage2 --backend=cranelift --jobs=full --output=build/bootstrap/s5`, `SIMPLE_TIMEOUT_SECONDS=0`.
STAGE2_RC=0
  Build complete: 752 compiled, 0 cached, 0 failed
  Linked: .../s5/stage2/x86_64-unknown-linux-gnu/simple (28385 KB) via clang++
  Stage 2 admitted; stopping before Stage 3 as requested.

### First attempt was killed externally
An identical first launch (`nohup`, not `setsid`) died with STAGE2_RC=143 (SIGTERM)
immediately after the seed build, no OOM in dmesg, no kill site in the script.
Re-launched under `setsid` and it survived. Anything long here must be `setsid`-detached.

## Advisory gate — RED
`sh scripts/check/check-stage2-option-unwrap-not-stolen.shs --stage2 build/bootstrap/s5/stage2/x86_64-unknown-linux-gnu/simple`
GATE_RC=1
  Segmentation fault (core dumped)
  FAIL -- 2 check(s) performed: 4 Simple '*_dot_unwrap' call site(s) inside lower_and_check_impl -- an Option unwrap bound to a user method instead of the runtime builtin; hello world emitted E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED (rc=139);

## Direct reproduction — 2-line hello world
`stage2/simple native-build hw.spl --runtime-path build/simple-core/libsimple_runtime.a -o hw.bin`
NB_RC=139 (SIGSEGV, core dumped)
  [build] mir 1/1 step 4/6 +256ms dt=146ms hw
  [ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module surface payload malformed at HIR entry (heap-typed payload word is 0 or in the zero page)

The parenthetical "(heap-typed payload word is 0 or in the zero page)" is NEW — earlier
attempts saw a bare rc=139. It names the zeroed-payload mechanism directly, consistent
with the known `.unwrap()`-binds-to-`Poll<T>.unwrap` root cause (returns 0 = "Some with a
zeroed payload"). This is the improved diagnostic the new trap/return fixes produced.

## Answer
Stage 3 cannot complete because the Stage 2 compiler it is built with CANNOT COMPILE ANY
PROGRAM: it segfaults at MIR lowering on a 2-line hello world. Failure is IDENTICAL in
kind to before (E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED, rc=139), with a strictly better
message.

## Reportable gate gap
Stage 2 was ADMITTED by the bootstrap's own sanity/admission gates ("running bootstrap
compiler sanity", "proving struct receiver/runtime capability") while being unable to
compile hello world. Those gates do not exercise a full native-build of a trivial program.

## dynload — not the cause
The log shows E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED, so the seed-driven Stage 2
build downgrades to one-binary. Same condition under which the previously-healthy Stage 2
was produced, and the failure reproduces on that one-binary Stage 2 compiling hello world.
Irrelevant to this defect.

## Full run — CONFIRMED (receipt-gated, no --stop-after, no --resume, fresh dir s5full)
Receipt minted via folded producer:
  `bootstrap-admission: produced .../admission/a9ab1083.../planner-admission-v2.env`
Validated BEFORE the long run (env var is `SIMPLE_BOOTSTRAP_REASON_RECEIPT`, not a flag):
  `bootstrap-policy: receipt-valid target=//bootstrap:stage4 reason=self-host-convergence-check execution=not-attempted` (rc 0)

FULL_RC=2. Verbatim:
  Stage 3: stage2 -> bootstrap_main.spl (self-host)
  Segmentation fault (core dumped)
  warning: stage3 self-host was KILLED by signal 11 (SEGV), not a compile failure; Stage 4 unavailable
  Stage 2 native-build capability passed
  Stage 3 unavailable - no provenance-verified compiler for Stage 4

Last lines of stage3-native-build.log (frontend all GREEN, dies at MIR lowering):
  [BOOTSTRAP-PHASE] +776825ms phase4:monomorphize:done
  [BOOTSTRAP-PHASE] +776825ms phase5:mode_dispatch:start
  [build] mir 0/0 step 4/6 +776825ms dt=0ms lower_to_mir
  [BOOTSTRAP-PHASE] +776825ms aot:lower_to_mir:start
  [mir-lower-free] start
  <SEGV, no further output>

NOTE FOR THE FIXING LANE: at Stage-3 scale the process SEGVs *before* the
E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED diagnostic is flushed; the 2-line hello-world
repro above is the one that prints the improved message. Use hello world, not Stage 3.

## Verdict
Stage 3 fails IDENTICALLY to before: same phase (aot:lower_to_mir), same signal 11 / rc 139.
Root cause is the already-root-caused `.unwrap()` -> `Poll<T>.unwrap` mis-binding (gate names
4 `*_dot_unwrap` call sites inside `lower_and_check_impl`). No new/different failure mode.

## Artifacts (kept for the fixing lane)
/mnt/data/worktrees/lane-boot-s5/build/bootstrap/s5      (Stage 2, admitted, 28385 KB)
/mnt/data/worktrees/lane-boot-s5/build/bootstrap/s5full  (full run, stage3 SEGV logs)
