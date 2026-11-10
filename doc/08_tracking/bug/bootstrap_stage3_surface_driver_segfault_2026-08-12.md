# Bug: admitted Stage2 segfaults while parsing the Stage3 driver surface

Date: 2026-08-12  
Status: open, reproduced once  
Severity: release blocker

## Failure

The isolated `packed-memory-build8` full Cranelift bootstrap produced and
admitted its self-hosted Stage2 compiler, then the Stage3 native build exited
139. The retained Stage3 log ends immediately after releasing the entry surface
and starting the second source:

```text
phase2:surface:file:start .../src/app/cli/bootstrap_main.spl seq=1
phase2:surface:file:released .../src/app/cli/bootstrap_main.spl seq=1
phase2:surface:file:start .../src/compiler/80.driver/driver.spl seq=2
```

No source diagnostic, core receipt, or stack trace was retained.

## Authoritative evidence

- Stage2 admission receipt:
  `/mnt/data/bs2/packed-memory-build8/stage3/x86_64-unknown-linux-gnu/stage2-sanity.env`
- Admitted Stage2 SHA-256:
  `2a3ccce93e1d4f316d64194c732f0f7d759ea76d751bb33a9b226803e0dfebb5`
- Stage3 command transcript:
  `/mnt/data/bs2/packed-memory-build8/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
- Stage3 log:
  `/mnt/data/bs2/packed-memory-build8/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- Terminal milestone: `exit-139`

The admitted artifact exposes only `compile` and `native-build`; it is not a
full CLI and cannot qualify RISC-V unit/GHDL specs.

## Next diagnostic

Do not rebuild Rust authority or discard the Stage2/Stage3 caches. Reproduce
the exact transcript once under a retained core/backtrace wrapper, first with
the same streaming-surface settings and then—only if the first receipt proves
the crash owner—with streaming release disabled. Preserve the core, executable
hash, environment transcript, last surface identity, and stack trace. Treat
`driver.spl` as the first observed victim, not yet the proven source owner.

## Triage 2026-11-10 (p3-boot3 lane, assignment row 20)

**Verdict: BLOCKED-needs-grant — verification-pending, no script owner in this lane.**

- The crash owner is the self-hosted compiler's streaming-surface parse
  (`src/compiler/80.driver`), which is outside this lane's bootstrap
  tooling/scripts scope; no `scripts/bootstrap` defect is identifiable from
  the retained evidence (no core/stack; `driver.spl` is a victim, not a
  proven owner).
- The 2026-10-27 ledger triage round already source-reviewed this row
  (`doc/08_tracking/bug/triage_20261027/evidence_v3/lane00_accepted.md`,
  accepted): the current streaming loop publishes `surface-released` only
  after parse/result handling and scope teardown ends transient allocation
  before replacing process-lifetime frontend globals — an ordering fix for a
  documented adjacent lifetime hazard — but there is no artifact/stack link
  from this report to that fix, so `keep_open` stands.
- Reproducing per the doc's "Next diagnostic" requires a full bootstrap to
  admit a Stage 2 compiler, then the Stage 3 transcript under a retained
  core. That is a HEAVY build, forbidden in this lane.

Exact command for the granted lane (Linux host, from the doc's transcript
settings):

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
ulimit -c unlimited
gdb -batch -ex run -ex bt --args \
  build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry src/app/cli/bootstrap_main.spl --entry-closure --threads 4 \
  -o build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
```

Preserve the core, executable sha256, environment transcript, last surface
identity, and backtrace; treat `driver.spl` as first observed victim until the
stack says otherwise. Related current tracker for the same surface-promote
path (perf, not crash): `stage3_quadratic_transient_heap_promote_2026-09-02.md`.

## Triage 2026-11-11 (P3 boot11 lane, work/p3-boot11-20261111)

**Verdict: BLOCKED-needs-grant — status stays OPEN.** Same posture as the
2026-10-27 ledger triage round (accepted, `keep_open`) and the 2026-11-10
p3-boot3 lane: the crash owner is the self-hosted compiler's
streaming-surface parse (`src/compiler/80.driver`), outside this lane's
bootstrap-script scope, and there is still no artifact/stack link from this
report to the 2026-10-27 surface-release ordering fix. This Windows lane
cannot run the retained-core reproduction (no admitted Stage 2 Linux binary;
full bootstrap + gdb repro is the heavy grant below).

Exact command for the granted lane (Linux host, per this doc's "Next
diagnostic"; do not discard Stage2/Stage3 caches):

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
ulimit -c unlimited
gdb -batch -ex run -ex bt --args \
  build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry src/app/cli/bootstrap_main.spl --entry-closure --threads 4 \
  -o build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
```

Preserve core, executable sha256, environment transcript, last surface
identity, and backtrace; treat `driver.spl` as first observed victim until the
stack says otherwise.
