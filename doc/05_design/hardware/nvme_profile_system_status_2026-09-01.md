# NVMe controller/media/board/offload profile system — implementation status

**Date:** 2026-09-01
**Plan:** `doc/03_plan/hardware/nvme_controller_profile_portability_plan.md`
**Goal:** G5 — "support a lot of open SSD controllers", previously at zero profiles.

## What now exists

| Deliverable | Status |
|---|---|
| Four-axis SDN schema (Controller x Media x Board x Offload -> ProductProfile) | done, `spec/profiles/` |
| Three real profiles with honest certification levels | done (3 boards, 3 controllers, 3 media, 3 offload) |
| Generator (validator + artifact emission + regeneration check) | done, `src/hardware/profiles/profile_gen.spl` |
| G5 core-untouched gate | done, `scripts/check/check-nvme-profile-core-untouched.shs` |
| Runnable portability check | done, `src/hardware/profiles/profile_portability_check.spl` |
| Origin ledger where `pending` blocks the build | done, `doc/08_tracking/hardware/nvme_profile_source_origin.sdn` |

D3 of the plan (deleting `TARGET_SIMPLE_SIM` and the `nvme_fw_target_config`
if-chain from `openssd_config.spl`) is **NOT done**: that file is core firmware
owned by another workstream. The generated `consts.spl` supersedes it, but the
deletion itself is a core edit and was deliberately not made.

## Profiles and their honest ceilings

| Board | Media reality | Ceiling | Substrate | Ledger |
|---|---|---|---|---|
| `SimpleFpgaRv32` | emulated (`dram_model`) | C3 — no real host, no NAND | **bound** (in-process emulator) | approved |
| `CosmosPlusReference` | real NAND (`raw_nand`) | C5 (C6 with rigs) — the only real-media candidate | declared, unbound | **pending — emission blocked** |
| `NvmeChaReference` | none (`block_backend`, controller test memory) | C4 — C5 would be a category error | declared, unbound | approved |

`certification_current: C0` on all three. Nothing has been exercised on hardware.

Provenance discipline: Cosmos+ apertures (`0x43C00000` stride `0x10000`,
`0x83C00000`), PCI identity `10EE:7028` and the bitstream SHA-256 are MEASURED,
from `cosmos_openssd_port_2026-06-30.md` and `spec/hw/cosmos_nfc/register_ir.sdn`.
Every other Cosmos and NVMeCHA number is marked `ILLUSTRATIVE` inline. **No PCI
IDs and no register layouts were fabricated** — the NVMeCHA profile declares
MMIO *windows* and states that its vendor/device IDs are unverified rather than
inventing them.

## Deviations from the plan, stated so they do not look accidental

1. **Layout.** The plan writes `profiles/` and `generated/<board>/` at an
   unspecified root. This lands at `spec/profiles/` and
   `spec/profiles/generated/<board>/`, the tree this workstream owns.
2. **Emitted artifact subset.** `consts.spl`, `caps.spl`,
   `conformance_params.sdn`, `aop_facts.sdn`, `profile.md`, `FINGERPRINT`. The
   RTL packages, linker fragment and devicetree of plan section 2.1 are not
   emitted — they need a BSP that does not exist yet.
3. **`FINGERPRINT` is not a SHA.** It is a content change detector for the
   regeneration gate, labelled `content-digest-v1`, and is deliberately not
   described as a cryptographic hash.
4. **Ledger scanning.** The nested SDN reader does not read table-form rows, so
   the ledger's two load-bearing columns are read by a line scanner.

## Environment defects found while building this (not caused by this work)

1. **This worktree cannot run any file-reading Simple program.** `core.sparseCheckout`
   is true with skip-worktree bits set across `src/lib`, leaving 98 of 8029
   stdlib files present as `.spl` (the rest as stale `.smf` stubs). Consequence:
   `std.common.sdn.parser` does not resolve and `std.fs.file_read_text` is not
   found — `src/hardware/ir/register_ir_gen.spl --check`, the *existing* proven
   generator, is equally broken here. This is the known shared-`.git` hazard.
   Everything below was therefore run in an isolated `git archive HEAD` tree with
   the example `fw/` copied in. The shared git config was NOT modified.
2. **SDN reader: an inline trailing comment breaks the value.** `blocks_per_plane: 64  # ILLUSTRATIVE`
   parses the value as 0. This silently zeroed six geometry fields and made two
   profiles' closure equations *pass vacuously* until caught. Worked around by
   putting comments on their own line; the parser bug is real and unfixed.
3. **SDN reader: `0x...` literals decode to 0.** Load-bearing here — the Cosmos+
   apertures are hex. `profile_gen.spl` decodes hex itself rather than reading
   every aperture as zero.

## Running it (from the REPO ROOT — `fw/nvme_transport_config.spl` uses a cwd-relative path)

    bin/simple run src/hardware/profiles/profile_gen.spl --list
    bin/simple run src/hardware/profiles/profile_gen.spl --validate
    bin/simple run src/hardware/profiles/profile_gen.spl --emit
    bin/simple run src/hardware/profiles/profile_gen.spl --check
    bin/simple run src/hardware/profiles/profile_portability_check.spl
    sh scripts/check/check-nvme-profile-core-untouched.shs --selftest-only
    sh scripts/check/check-nvme-profile-core-untouched.shs BASE..NEW

Verdict is the LAST line of stdout in every case. **Exit codes are not
evidence** — `bin/simple run` returns 193 for a successful program.
