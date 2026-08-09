# T1 — Self-Hosted Re-verification of Modern SSpec Results (2026-08-09)

Source: `doc/03_plan/infra/sspec/modern_sspec_completion_plan_2026-08-09.md`, task T1.

## Goal

Every Modern SSpec verification to date ran on the disclosed Rust bootstrap
SEED binary. Repo policy requires the pure-Simple self-hosted binary for
`test`/`lint`/`fmt`/`build`/`run`. Determine whether a self-hosted
re-verification is achievable right now, and if so perform it.

## Step 0 — Safety gate (2026-08-09T01:36Z)

- **Disk**: `df -h /` → `/dev/nvme0n1p2 3.7T 3.6T 62G 99% /`. 62G free, above
  the 25G STOP threshold. Not a blocker by itself, but the filesystem is at
  99% utilization with other sessions active — a full bootstrap can consume
  large scratch space and risks tipping this over.
- **Competing bootstraps already running** (`pgrep -af "simple build|bootstrap|cargo"`):
  - PID 721957: `stage2-simple native-build --entry src/app/cli/bootstrap_main.spl -o build/probe2/stage3-simple` (from a sibling worktree `simple-s3clean`)
  - PID 1020782/1020787/1020788: `stage2-runtime-authority/simple native-build ... -o /tmp/simple-runtime-abi-enum553/build/stage3-enum-owner-admission/stage2/simple` (under a 1800s timeout wrapper)
  - PID 1054024: `src/compiler_rust/target/bootstrap/simple native-build ... -o build/mini_builds/imported-callable-stage3/phase2-simple` — this one runs directly in THIS repo's tree (`/home/ormastes/dev/pub/simple`)
  - Per task instructions: "if another session is ALREADY running a bootstrap, do NOT start a competing one." Multiple are running, including one in this exact repo tree. **Did not start a new bootstrap.**
- **Current deployed binary identity**: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`.
  `bin/simple --version` prints:
  ```
  WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
  Build and use the pure-Simple bin/simple instead.
  Simple Language v1.0.0-beta
  ```
  This is a **self-disclosed SEED binary**, not self-hosted.
- **Existing self-hosted binary check**: `ls -la bin/release/*/simple*` shows
  only one file: `bin/release/x86_64-unknown-linux-gnu/simple` (29,573,408
  bytes, mtime Aug 8 12:14) — the same seed binary above. No non-seed
  self-hosted binary is currently deployed anywhere under `bin/release/`.

## Verdict

**T1 BLOCKED — no competing build started.**

Reasons:
1. No self-hosted binary is currently deployed to reuse (step 0 found only
   the seed at `bin/release/x86_64-unknown-linux-gnu/simple`).
2. A fresh bootstrap was NOT attempted because other sessions already have
   bootstrap/native-build jobs in flight against overlapping trees — most
   notably PID 1054024 running directly in this repo
   (`/home/ormastes/dev/pub/simple`) via
   `src/compiler_rust/target/bootstrap/simple native-build ... --entry
   src/app/cli/bootstrap_main.spl -o
   build/mini_builds/imported-callable-stage3/phase2-simple`. Starting a
   second concurrent bootstrap risked resource contention and disk pressure
   on an already-99%-full filesystem (62G free).
3. Steps 1-3 (build, self-hosted verification of the evidence/docgen specs,
   and positive capability-probe identity check) were therefore not
   performed this run.

## Resume command

Once no `simple build|bootstrap|cargo` bootstrap processes are running
(re-check with `pgrep -af "simple build|bootstrap|cargo"`) and disk free on
`/` stays comfortably above 25G, resume with:

```bash
# Step 0 re-check
df -h /
pgrep -af "simple build|bootstrap|cargo"
ls -la bin/release/*/simple*

# Step 1 — build (per .claude/rules/bootstrap.md)
bin/simple build bootstrap 2>&1 | tee /tmp/claude-1000/-home-ormastes-dev-pub-simple/93f9b900-8e65-4a83-b9d7-c9a85fbe5ecf/scratchpad/t1_bootstrap.log

# Step 2 — positive capability probe (subcommand the seed lacks)
bin/release/x86_64-unknown-linux-gnu/simple sspec-maintain --help

# Step 2 — re-run specs on the confirmed self-hosted binary
bin/simple test test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl   # expect 28/28
bin/simple test test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl            # expect 21/21
bin/simple test test/01_unit/lib/common/spec/evidence/exec_capture_spec.spl             # expect 6/6
sh scripts/check/check-spipe-docgen-regeneration-live.shs                               # expect PASS 4/4
bin/simple test test/03_system/tools/spipe/examples/live_terminal_capture_spec.spl
bin/simple test test/03_system/tools/spipe/examples/live_json_capture_spec.spl
bin/simple test test/03_system/tools/spipe/examples/live_text_protocol_capture_spec.spl
bin/simple test test/03_system/tools/spipe/examples/live_binary_capture_spec.spl
```

## Status

**T1 NOT SATISFIED** — blocked on: (a) no self-hosted binary currently
deployed, (b) concurrent in-repo bootstrap activity from other sessions that
made starting a new one unsafe at time of check (2026-08-09T01:36Z). No
specs were re-run under this task; do not cite this run as self-hosted
verification.
