# rv64 DTB overlay is not materialized in the SoC address map (`addr4g_probe`)

**Status:** open
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane B)
**Area:** `src/lib/hardware/soc_rtl/` — `dtb_asset.spl`, `bootrom.spl`
**Severity:** medium — a real model defect, previously **masked** by a toolchain bug

## Finding

`addr4g_probe` fails its rv64 DTB overlay assertions:

- the magic byte at `0x8800_0000` reads `0xD0` instead of the expected DTB magic
- the read-only assertion on the overlay region also fails

The overlay is declared at `src/lib/hardware/soc_rtl/dtb_asset.spl:10` and
referenced from `bootrom.spl:62`, but it is **never materialized into the rv64 SoC
address map**, so reads at the overlay base return whatever the underlying map
provides.

## Why this was not caught earlier

This is the interesting part. `addr4g_probe` **could never execute** before
2026-07-27: it aborted during compilation with
`error: semantic: variable 'hardware' not found`, because the Rust bootstrap
seed's interpreter directive skip list omitted `hardware` (see
`interpreter_eval.rs:606-619`). Every run died before reaching a single assertion.

Fixing that seed gap turned the probe from *unrunnable* into *running and failing*.
**The defect was not introduced — it was uncovered.** A gate that cannot run
provides no assurance, and its silence had been indistinguishable from a pass.

This is a concrete instance of the campaign's standing rule that a gate's *ability
to execute* must be verified separately from its verdict.

## Reproduction

```bash
cd /home/ormastes/dev/pub/simple
SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple \
  sh scripts/check/check-riscv-hardware-gates.shs 2>&1 | grep addr4g
# or directly:
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpreter \
  bin/simple run test/01_unit/lib/hardware/soc_rtl/addr4g_probe.spl
```

Requires a seed built with the `@hardware` directive fix, or a redeployed
pure-Simple binary — see
`doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md`.

## Scope note

`addr4g_probe` is registered as an **optional** gate in
`scripts/check/check-riscv-hardware-gates.shs`, so it does not currently block the
bundle's headline count. That optional status should be revisited once the overlay
is materialized — an optional gate that has never run is not evidence of anything.

## Suggested fix

Materialize the DTB overlay into the rv64 SoC address map so `0x8800_0000` returns
the asset bytes with read-only semantics, matching what `bootrom.spl:62` assumes.
Verify against an absolute oracle (the expected DTB magic), not by comparing the
map to itself.

## Related

- `doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md`
- `doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md`
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
