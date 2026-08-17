# RISC-V gate evidence is seed-attributed — `bin/release/<triple>/simple` is a Rust seed

**Status:** open (blocker row, not a defect in the gates themselves)
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

## 2026-08-17 — FIXED (provenance now stated in the verdict)

RED reproduced first, on the live tree:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
```

`scripts/check/check-riscv-hardware-gates.shs` printed only `simple binary:
<path>` and then `RISCV-HW-GATES: n/m PASS` — no engine identity anywhere, so a
green line read as a self-hosted result when it was the Rust seed.

Fix (same file):
- `classify_engine()` probes `--version` **before any gate runs**, assigning rc
  on the line AFTER the command (never through a pipe), and classifies
  `rust-seed` / `self-hosted`.
- An indeterminate binary (nonzero `--version`, or empty output) is
  `ERROR — nothing was checked` exit 2. Absence of evidence is never a pass.
- The engine is carried into the terminal verdict:
  `PASS — <n> gate(s) checked, 0 failed (engine=rust-seed)` /
  `FAIL — <n> gate(s) checked, <k> failed (engine=...)`.
- `TOTAL == 0` is now `ERROR ... exit 2`, not exit 1.
- `--selftest` (fatal, 4 shim fixtures): seed banner must classify as
  `rust-seed`; a non-seed banner as `self-hosted`; an unrunnable binary and a
  silent `--version` must both be indeterminate, never `self-hosted`.

After:

```
$ sh scripts/check/check-riscv-hardware-gates.shs --selftest | tail -1
PASS — 4 selftest fixture(s) checked
$ sh scripts/check/check-riscv-hardware-gates.shs --bogus; echo rc=$?
ERROR — nothing was checked: unknown argument '--bogus'
rc=2
$ sh scripts/check/check-riscv-hardware-gates.shs | grep '^engine:'
engine: rust-seed (59536728 bytes, mtime 2026-08-16 22:59:37 +0000)
```

The underlying condition (this machine has no self-hosted binary deployed) is
unchanged and still tracked by
`no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md`; what is
fixed here is the misattribution.
