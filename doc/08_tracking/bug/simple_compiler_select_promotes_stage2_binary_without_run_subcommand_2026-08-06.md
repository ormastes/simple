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
