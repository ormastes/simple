# simple_compiler_select promotes a stage-2 binary with no `run` subcommand (and segfaults twice on the way)

- **Date:** 2026-08-06
- **Status:** OPEN — needs a bootstrap / compiler-deployment owner
- **Found by:** guard-wiring fail-open follow-up (`6ad2cda325c`), while making
  `check-riscv-fpga-sidecar-contract.shs` report its failures instead of dying
  silently.
- **Scope:** `scripts/lib/simple-compiler-select.shs`, the deployed binaries
  under `bin/release/` and `build/bootstrap/stage2/`. NOT a RISC-V problem.

## Symptom

Three guard scripts were filed in
`doc/08_tracking/bug/guard_wiring_optout_false_exemptions_2026-08-06.md` as RED
with a shared root cause labelled "riscv-fpga-sidecar-contract self-test". That
label was wrong twice over. The self-test failure was a non-hermetic fixture
(fixed in `6ad2cda325c`), and behind it sat this, which is not riscv-specific:

```
$ sh scripts/check/check-riscv-fpga-sidecar-contract.shs
STATUS: FAIL riscv-fpga-sidecar-contract reason=bundle-generation-failed
  out=.../build/riscv_fpga_sidecar_contract/default exit=1
  compiler=.../build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
-- generator stdout --
error: unknown command 'run'
```

## Root cause

`simple_compiler_select` returns
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, and that binary has
no `run` subcommand:

```
$ build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple run --help
error: unknown command 'run'
```

So every guard that selects a compiler this way and then invokes
`"$SIMPLE_BIN" run <script>.spl` fails, regardless of what it is checking.

Two further facts found while probing, each its own defect:

1. **`simple_compiler_select` prints `Segmentation fault` TWICE on stderr and
   still returns a path with exit 0.** The selector is crashing candidates
   during its probe and reporting success. A positive-capability probe that
   segfaults its candidates must not then promote one of them.

2. **`bin/release/simple` is a 2181-byte wrapper that refuses to run**:
   `error: refusing non-production Simple runtime:
   bin/release/x86_64-unknown-linux-gnu/simple`. This is what made the sidecar
   self-test non-hermetic — the wrapper's nonzero exit put the seed-identity
   probe into its fail-closed branch, so the real self-hosted binary was
   classified as a Rust seed. Related prior art:
   `reference_live_bin_simple_lost_all_subcommands_2026-08-01`.

## Why this is filed and not fixed

The fix is in the bootstrap / compiler-deployment lane, which was active with a
Stage-3 investigation at the time. Working around it inside the guard scripts
would mean either selecting a different binary or skipping the generation step
— both would weaken the gates to get green, which repo policy forbids. The
guards now report the failure loudly and precisely instead.

## Affected gates

- `check-riscv-fpga-sidecar-contract.shs` — main path
- `check-riscv-formal-dual-track.shs` — via the above
- `check-riscv-rtl-sby-proof.shs` — via the above
  (`reason=sidecar-contract-failed`)
- `check-simpleos-byl-sby-artifacts.shs` — **now GREEN**; it was red only on
  the non-hermetic self-test, not on this.

Any other guard doing `simple_compiler_select` + `"$SIMPLE_BIN" run` is
presumably affected; that set has not been enumerated here.

## Repro

```sh
sh -c '. scripts/lib/simple-compiler-select.shs; simple_compiler_select --root "$PWD" --quiet'
# -> Segmentation fault (x2 on stderr), then the stage2 path, exit 0
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple run --help
# -> error: unknown command 'run'
```

## Amendment 2026-08-06 (app/i18n lane, seed-path evidence)

**Claim 1 above ("segfaults twice and still returns exit 0") is WRONG — retracted.**
The two bare `Segmentation fault` lines are the probe *working*. The selector's
own `--self-test` predicts rc=139 on exactly two candidates it must reject —
`bootstrap/stage3/x86_64-unknown-linux-gnu/simple` and `bootstrap/stage2/simple`
— and those are the two crashes observed. A probe that kills a known-bad
candidate and then promotes a surviving one is fail-CLOSED behaviour, not a
defect. Exit 0 with a path on stdout is the documented success contract.

**The real defect is a contract divergence, and it is worse than filed.**
The file header (lines 35-41) states the core tier means *"a host compiler that
can run a .spl"*. The probe never tests `run`: its ladder is `check p.spl` then
`native-build --entry p.spl`. So the tier advertises a capability it does not
measure, and callers doing `"$SIMPLE_BIN" run <script>.spl` get the promoted
binary's `error: unknown command 'run'` instead of a selection failure.

**New fact not in the original report: NO staged binary in this tree implements
`run` at all.** Measured on every default candidate:

| candidate | `run --help` |
|---|---|
| `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | `error: unknown command 'run'` |
| `bootstrap/stage3/simple` | `error: unknown command 'run'` |
| `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` | `error: unknown command 'run'` |
| `bootstrap/stage2/simple` | `error: unknown command 'run'` |
| `release/x86_64-unknown-linux-gnu/simple` | SIGSEGV (core dumped) |
| `bin/release/*-unknown-simpleos/simple` | SIGSEGV / cross-target |
| `bin/release/x86_64-unknown-linux-gnu/simple` | works — but it is the Rust seed, rejected by identity |

Root cause of the absence: `src/app/cli/bootstrap_main.spl:449-484` is the
staged compilers' `main`. It dispatches `native-build`, `compile`, `--version`
and `--help`, and nothing else — `run` was never part of the bootstrap CLI.

Consequence: the **19** scripts that call `simple_compiler_select` and then
`"$SIMPLE_BIN" run` are structurally red regardless of which candidate is
promoted. Changing the selector cannot make them green; there is no binary for
it to find. Fix options, none of which belong to a guard-script lane:

1. Add `run` to `src/app/cli/bootstrap_main.spl` (then rebuild stage2/stage3).
2. Give the selector an explicit `--require run` tier AND wire the 19 callers,
   so they fail early with "no compiler can run a .spl" instead of late with
   "unknown command 'run'".

Option 2 alone is honesty, not a fix. Option 1 is the actual repair.

**Not attempted here** because verifying either requires a stage2/stage3
rebuild, and two Stage 3 builds were already live on this host.
