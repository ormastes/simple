# RISC-V gate evidence is seed-attributed — `bin/release/<triple>/simple` is a Rust seed
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** BLOCKED 2026-11-11 (lane p3-seedA) — blocker row confirmed, not a defect in
  the gates themselves. Header flipped from "open". The seed-attribution finding still
  holds at the lane base (`bin/simple.exe --version` prints the Rust-seed warning banner,
  build-commit 46fe8f6b6def); no source change can alter *binary attribution* — only a
  sanctioned whole-compiler bootstrap + redeploy can, which is forbidden in this lane
  (tracked `bin/simple.exe` stays; T3 gate; needs a quiescent host). Grant re-recorded
  verbatim in the dated addendum below.
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane H)
**Area:** bootstrap / deploy — `bin/release/x86_64-unknown-linux-gnu/simple`
**Severity:** medium — blocks *release attribution* of every RISC-V gate result,
does not by itself change any gate verdict

## Finding

`bin/simple` resolves to `bin/release/x86_64-unknown-linux-gnu/simple`, and that
binary is a **Rust-built bootstrap seed**, not the pure-Simple self-hosted
compiler:

```
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta

$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
$ ls -la bin/release/x86_64-unknown-linux-gnu/simple
-rwxrwxr-x 145290352 2026-07-25 .../simple          # 145 MB Rust build
-rwxr-xr-x  47579568 2026-07-25 .../simple_seed     # sibling present
```

The `simple_seed` sibling IS present, so the `cli_symlink_argv0_seed_sibling`
self-delegation loop does not apply here.

## Impact

Per `.claude/rules/bootstrap.md` ("Default tooling runs on pure-Simple") and the
SPipe binary-identity rule, evidence produced by a seed is attributable to the
SEED, not the self-hosted compiler. Everything measured in this campaign is
therefore **seed-attributed** and cannot close a release claim:

| Gate | Exit (seed) | Result |
|---|---|---|
| `check-riscv-rtl-truth.shs` | 0 | `ok=true`, unknown=0 |
| `check-riscv-hardware-gates.shs` | 1 | `RISCV-HW-GATES: 12/22 PASS` |
| `check-riscv-formal-dual-track.shs` | 1 | `variable 'hardware' not found` |
| `check-riscv-product-level-evidence.shs` | 1 | `FAIL riscv_fpga_linux_spec.spl` |

Also seed-attributed: the KV260 JTAG-console completeness evidence landed the
same day (`COMPLETE: emitted=568 captured=568 lost=0`).

The red gates are almost certainly real regardless of binary — they fail at
parse/semantic/lowering time on source, not on compiler codegen. But that is an
argument, not evidence, until re-run.

## Why not fixed in this session

Redeploying requires a bootstrap, which is a **T3** gate (the highest
verification tier) and is the known-hard whole-compiler redeploy — see the
recurring "#99 whole-compiler redeploy — do NOT race" note and
`reference_stage4_bootstrap_killed_by_resource_monitor_64gb_cap`. Stage 4 has
peaked at ~65 GB RSS and been SIGTERM'd by the 64 GB monitor cap. Seven agents
were compiling concurrently when this was found; starting a bootstrap into that
would thrash the host and produce an unreliable result either way.

This is a deliberate **blocked** row with a resume plan, not a postponement
dressed as completion.

## Resume plan

- **Owner:** bootstrap/deploy lane
- **Prerequisite:** quiescent host (no parallel agent compiles), ≥64 GB headroom
  or the resource-monitor cap raised for the run
- **Exact resume command:**
  ```bash
  scripts/setup/setup.shs && bin/simple build bootstrap
  # then re-verify attribution:
  bin/simple --version          # must NOT print the seed warning banner
  readlink -f bin/simple
  ```
- **Then re-run, in this order, and re-record every row:**
  ```bash
  sh scripts/check/check-riscv-rtl-truth.shs
  sh scripts/check/check-riscv-hardware-gates.shs
  sh scripts/check/check-riscv-formal-dual-track.shs
  sh scripts/check/check-riscv-product-level-evidence.shs
  ```
- **Retained artifacts:** `build/riscv_hw_gates/*.log`, and the gate stdout
  captured under the campaign's scratch dir.

## Related

- Recurring seed-clobber of `bin/release/<triple>/simple` is a known pattern; a
  prior campaign worked around it with a scratch-named lane binary
  (`build/native_probe/simple`, present here, dated 2026-07-23).
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
- SPipe state: `.spipe/simple_riscv_hardening/state.md`


## 2026-11-11 addendum (lane p3-seedA) — BLOCKED, resume-plan grant intact

Lane p3-seedA re-verified this row during the P3/P2/P1 bug-fix campaign and
confirmed it is a pure infra/attribution blocker, not a `src/compiler_rust`
code defect. Re-verified at the lane base (worktree cut from
`origin/release/1.0.0` tip `79d5af6723f6`, which already includes the comp9
verdict work):

- The tracked seed still self-identifies as a Rust seed:
  `bin/simple.exe --version` prints the `WARNING: this Rust-built Simple binary
  is a bootstrap seed only` banner, `build-commit: 46fe8f6b6def`. So every
  RISC-V gate result produced through `bin/simple` remains **seed-attributed**;
  the Finding is unchanged.
- No edit to `src/compiler_rust/**` can change *which binary* `bin/simple`
  resolves to. Attribution flips only when the pure-Simple self-hosted binary
  is built and deployed over `bin/release/<triple>/simple` — a T3-gated
  whole-compiler bootstrap.
- Lane constraints make that impossible here: the campaign setup forbids
  touching the tracked `bin/simple.exe` ("deployed seed stays"), no push/PR is
  allowed, and the doc's own "Why not fixed" note records that a redeploy needs
  a quiescent host (no concurrent agent compiles) plus ≥64 GB headroom or a
  raised resource-monitor cap — conditions this lane cannot establish.

Grant integrity check: the "Resume plan" section above is present and complete;
no absorber commit exists (`git log --all --grep` for this bug id finds only
this doc). The related `simple_seed` sibling and the `build/native_probe/simple`
scratch-lane binary noted under "Related" are context, not a fix.

Verbatim grant (re-recorded intact from the "Resume plan" above):

- **Owner:** bootstrap/deploy lane
- **Prerequisite:** quiescent host (no parallel agent compiles), ≥64 GB headroom
  or the resource-monitor cap raised for the run
- **Exact resume command:**
  ```bash
  scripts/setup/setup.shs && bin/simple build bootstrap
  # then re-verify attribution:
  bin/simple --version          # must NOT print the seed warning banner
  readlink -f bin/simple
  ```
- **Then re-run, in this order, and re-record every row:**
  ```bash
  sh scripts/check/check-riscv-rtl-truth.shs
  sh scripts/check/check-riscv-hardware-gates.shs
  sh scripts/check/check-riscv-formal-dual-track.shs
  sh scripts/check/check-riscv-product-level-evidence.shs
  ```
- **Retained artifacts:** `build/riscv_hw_gates/*.log`, and the gate stdout
  captured under the campaign's scratch dir.

Disposition: BLOCKED. Header flipped open → BLOCKED 2026-11-11 (lane p3-seedA).
