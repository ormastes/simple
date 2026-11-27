# rv64 DTB overlay is not materialized in the SoC address map (`addr4g_probe`)
## Resolved 2026-11-25 — overlay now served from the generated asset; `addr4g_probe` ALL PASS

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** resolved 2026-11-25 (see resolution section at the bottom)
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


## Resolution — 2026-11-25 (release/1.0.0)

**Reproduced live before the fix** on the pinned Windows seed:
`SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpreter bin/simple run
test/01_unit/lib/hardware/soc_rtl/addr4g_probe.spl` →
`FAIL rv64 DTB overlay magic byte @0x88000000 == 0xD0`,
`FAIL rv64 DTB overlay is read-only`, `ADDR4G_PROBE: 2 FAIL` (all other
assertions green).

**Root cause.** `soc64_dtb_read` (`src/lib/hardware/soc_rtl/soc_top_64.spl`)
assembled reads from `soc.ram` at `SOC64_DTB_BASE - SOC64_RAM_BASE + off`.
That only works when DRAM is large enough to contain the DTB window AND
`soc_top_64_sim_preload_dtb` was called (the protected 256 MiB configs). Any
smaller simulation RAM — the probe uses 4 MiB — cannot hold the blob at
offset 128 MiB, so the "overlay" read fell through to empty RAM and returned
0 instead of the FDT magic. The write side was already correct (writes into
the window are ignored before the DRAM check).

**Fix.** `soc64_dtb_read` now materializes the bytes on demand from the
generated asset — exactly the boundary `dtb_asset.spl`'s header documents
("this module is the ROM boundary that materializes bytes on demand") — via
`soc_rv64_linux_dtb_for_ram_initrd` + the existing `soc_dtb_byte` helper,
composing `width_bytes` little-endian. This returns byte-identical values to
the old path in every configuration where the old path was correct (the
preload loads the same generated blob into RAM), and is correct in every
other configuration. Verified against an absolute oracle (the 0xD00DFEED
magic), not by comparing the map to itself.

**Evidence after the fix (same host, same commands):**
- `addr4g_probe.spl`: `ADDR4G_PROBE: ALL PASS` (both former FAILs now PASS,
  all rv32/rv64 dispatch assertions unchanged).
- Protected-path regression probe replicating
  `soc_top_64_protected_spec.spl`'s DTB assertions
  (`soc_top_64_sim_preload_dtb(soc_top_64_protected_init())` +
  `soc64_accept_core_request`): DTB write still errors and is ignored, DTB
  read still returns `0xEDFE0DD0`, RAM at 0x0800_0000 untouched — PASS.

**Limit / follow-up.** The spipe specs themselves
(`soc_top_64_protected_spec.spl`, `soc_dtb_asset_spec.spl`) could not be run
end-to-end here (pinned seed rejects `@representation_boundary` at
release/1.0.0 HEAD); the protected-path probe above covers their DTB
assertions. Per-read regeneration of the blob is a deliberate
correctness-first choice on a simulation read path; if a cycle-level Linux
boot gate ever profiles it hot, cache the blob at the harness level rather
than reintroducing a RAM-window dependency. The doc's scope note about
promoting `addr4g_probe` from an optional gate to a required one remains an
owner decision and was not changed here.
