# NVMe Controller Profile Portability Plan (Workstream C, G5)

**Date:** 2026-09-01
**Parent:** `nvme_complete_fw_mdsoc_offload_master_plan.md` §4 (G5), §9-C
**Design source:** `nvme_ssd_firmware_hardening_design_plan.md` §1 (C0–C6), §8
**Status:** Plan. Nothing below describes code that exists.

---

## 0. Current truth, measured

The profile system is **UNBUILT**. Verified on this tree, 2026-09-01:

1. **No profile module exists.** `grep -rln 'ControllerProfile\|MediaProfile\|BoardProfile\|OffloadProfile'` over `src/` and `examples/` returns only unrelated subsystems — `src/lib/nogc_sync_mut/database/offload_profile.spl`, `web_db_offload/web_profile.spl`, `hardware/fpga_linux/*`. Zero NVMe hits. Zero `.sdn` profile files.
2. **One hardcoded target.** The single target axis is an `i64` constant:

   | site | content |
   |---|---|
   | `examples/09_embedded/simpleos_nvme_fw/fw/openssd_config.spl:11` | `val TARGET_SIMPLE_SIM: i64 = 0` |
   | `openssd_config.spl:45`, `:206`, `:228`, `:235` | default config record, `nvme_fw_target_config` dispatch, self-check |
   | `fw/nvme_controller.spl:67`, `:85` | `nvme_controller_new_for_target(TARGET_SIMPLE_SIM)` |
   | `fw/firmware.spl:30`, `:197` | `firmware_new_for_target(TARGET_SIMPLE_SIM)` |

   **Correction to the task brief:** the constant is in `fw/openssd_config.spl`, **not** `fw/nvme_types.spl`. `nvme_types.spl` contains no `TARGET_` symbol at all. The brief's file pointer was off by one file; the substance (one hardcoded target, no profiles) is confirmed.
3. `openssd_config.spl`'s `nvme_fw_target_config(target_id)` if-chain is exactly the mechanism this plan supersedes. It is an in-source switch on an integer: adding a controller today means editing core firmware, which is the G5 failure this workstream must eliminate.

Related in-repo asset: `doc/03_plan/hardware/cosmos_openssd_port_2026-06-30.md` already records real Cosmos+ register bindings (NFC apertures `0x43C00000`+`0x10000`×8, PCIe aperture `0x83C00000`, host id `10EE:7028`, bitstream hash contract). That document is the seed for the Cosmos+ profile, not a substitute for it.

---

## 1. Profile schema in SDN

This repo uses SDN for configuration (`src/lib/simple.sdn` nested form; `doc/08_tracking/todo/todo_db.sdn` table form). Profiles use the nested form; ledgers and certification records use the table form.

### 1.1 Layout

```text
profiles/
  controller/<name>.sdn      # silicon/fabric: CPU, MMIO, DMA, IRQ, protection, transport
  media/<name>.sdn           # NAND part class or block backend
  board/<name>.sdn           # wiring: controller x media x offload, + evidence bar
  offload/<name>.sdn         # which @hw units are in circuit on this product
bsp/<controller>/            # hand-written: reset, clock, cache, MMIO/DMA/IRQ services
generated/<board>/           # generator output ONLY — never hand-edited
```

Four axes, one product. `board` is the only file that composes; `controller`, `media`, `offload` never reference each other.

### 1.2 Real example — a complete board

`profiles/board/cosmos_plus_reference.sdn`:

```sdn
# Cosmos+ OpenSSD reference product profile.
# Composes controller x media x offload. Generated outputs land in
# generated/cosmos_plus_reference/ and are never hand-edited.

schema_version: 1

board:
  id: CosmosPlusReference
  revision: "cosmos-plus-8ch8way-v3.0.0"
  controller: CosmosPlusZynq7000
  media: ToshibaOnfiToggle
  offload: CosmosNfcEccDma

  wiring:
    channels: 8
    ways_per_channel: 8
    # Upstream PL binding; see cosmos_openssd_port_2026-06-30.md
    nfc_aperture_base: 0x43C00000
    nfc_aperture_stride: 0x10000
    pcie_aperture_base: 0x83C00000
    pcie_aperture_span: 0x10000

  identity:
    pci_vendor: 0x10EE
    pci_device: 0x7028
    pci_class: 0x010802
    bar0_bytes: 8192
    # PL has no trustworthy runtime identity register; bind the bitstream hash.
    bitstream_sha256: "66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2"
    bitstream_contract: COSMOS_PCIE_CONTRACT_8CH8WAY_V300

  evidence_required: C5
  certification_current: C0
  unsupported:
    - sgl
    - zns
    - controller_memory_buffer
```

`profiles/controller/cosmos_plus_zynq7000.sdn`: (the apertures, PCI identity and bitstream hash are MEASURED, from `cosmos_openssd_port_2026-06-30.md`; the queue/depth/spec-ceiling numbers are illustrative until the profile is authored against the Zynq TRM and upstream PL project)

```sdn
schema_version: 1

controller:
  id: CosmosPlusZynq7000
  soc: "Xilinx Zynq-7000 XC7Z045"

  cpu:
    isa: armv7a
    endian: little
    harts: 2
    atomic_width: 32
    fpu: vfpv3

  address:
    physical_bits: 32
    dma_bits: 32

  nvme:
    transport: pcie
    generation: gen2
    lanes: 8
    spec_ceiling: "1.3"
    queues:
      admin: 1
      io_max: 8
      depth_max: 256
    outstanding_max: 128
    prp: multi_page
    sgl: false

  mmio:
    # Register description is IMPORTED, never transcribed by hand into .spl.
    registers: import_systemrdl("rtl/cosmos_pcie_nvme.rdl")
    windows:
      - name: pcie_host
        base: 0x83C00000
        span: 0x10000
        access: rw
      - name: nfc_channel
        base: 0x43C00000
        span: 0x80000
        access: rw

  dma:
    coherent: false
    descriptors: 64
    max_transfer: 65536
    alignment: 64
    cache_maintenance: explicit

  irq:
    mode: gic
    controller: gicv1
    vectors: 96

  protection:
    mpu_regions: 8
    axi_firewall: true
    iommu: none

  memory:
    firmware_region: 0x00100000..0x00500000
    mailbox_region:  0xFFFFF000..0xFFFFF100
    data_region:     0x10000000..0x40000000
```

`profiles/media/toshiba_onfi_toggle.sdn`:

```sdn
schema_version: 1

media:
  id: ToshibaOnfiToggle
  kind: raw_nand            # raw_nand | block_backend | dram_model
  interface: toggle_1_0
  cell: mlc

  geometry:
    luns_per_way: 1
    planes_per_lun: 2
    blocks_per_plane: 4096
    pages_per_block: 256
    page_bytes: 16384
    oob_bytes: 1280

  timing_ns:
    read_page: 60000
    program_page: 1300000
    erase_block: 3800000
    transfer_byte: 6

  ecc:
    scheme: bch
    correctable_bits_per_1k: 40
    parity_bytes_per_page: 1024

  reliability:
    program_erase_cycles: 3000
    read_retry_levels: 7
    requires_read_disturb_scan: true
    requires_data_retention_scan: true

  # Runtime discovery may NARROW these; never exceed them. (hardening §2.2.7)
  discovery:
    onfi_parameter_page: required
    narrowing_allowed: true
```

`profiles/offload/cosmos_nfc_ecc_dma.sdn`:

```sdn
schema_version: 1

# The OffloadProfile is the master plan's new axis (§2, §4): which @hw-tagged
# units are in CIRCUIT on this product. Same firmware source either way.
offload:
  id: CosmosNfcEccDma
  units:
    ecc_encode:        circuit    # circuit | firmware
    ecc_decode:        circuit
    prp_walk:          firmware
    queue_fetch:       firmware
    completion_post:   firmware
    dma_scatter:       circuit
    nand_scheduler:    firmware
    lba_hash:          firmware
    gc_victim_scan:    firmware
  differential_required: true     # G4: circuit and firmware forms must agree
```

For contrast, an OpenExpress-class frontend inverts the top four rows to
`circuit` with no change to any firmware source file — that is the point of the
axis.

---

## 2. Generator contract

### 2.1 Inputs and outputs

One command, `simple nvme-profile-gen <board>`, reads the four SDN files plus imported register descriptions and emits into `generated/<board>/`:

| Output | Content |
|---|---|
| `consts.spl` | semantic constants and bounded types (`Ppn<Board>`, `Lba`, `QueueId`, channel/way/lun/plane/block/page coordinate types) |
| `registers.spl` | typed MMIO accessors per register with access mode (`ro`, `rw`, `w1c`, `doorbell`, `fifo`), reset values, reserved-bit masks |
| `caps.spl` | controller and media capability traits (`HasSgl`, `HasIommu`, `RawNandMedia`, `BlockBackendMedia`) |
| `dma_layout.spl` | descriptor layouts plus static alignment assertions |
| `memory.ld` | linker script fragment: sections, regions, region-overflow assertions |
| `protection_init.spl` | startup PMP/MPU/firewall/IOMMU tables |
| `<board>_pkg.vhd`, `<board>_pkg.sv` | RTL packages and testbench constants (same numbers as firmware sees) |
| `aop_facts.sdn` | allowed access regions, capability facts consumed by the AOP verifier |
| `conformance_params.sdn` | test parameter sets (queue counts, depths, transfer sizes, timing bounds) |
| `devicetree.dtsi` | Linux PCI-endpoint metadata, emitted only for `transport: pcie_endpoint` targets |
| `profile.md` | generated documentation |
| `FINGERPRINT` | SHA-256 over all of the above plus input hashes |

### 2.2 Validation before emission

The generator rejects a profile whose equations do not close, evaluated in a wide compile-time integer domain (hardening §8.3):

```text
num_pages = channels x ways x luns x planes x blocks x pages_per_block
namespace_capacity_lbas <= usable_pages x sectors_per_page
metadata_bytes_per_page <= oob_bytes - ecc.parity_bytes_per_page - reserved
max_inflight_writes x per_write_buffers <= write_buffer_pool
io_max x depth_max <= command_context_capacity
address.dma_bits >= bits(max configured DMA window)
every mmio register offset fits its declared window; windows do not overlap
protection regions representable and non-overlapping
hard_realtime_reserved_slots + background_max <= total_slots
journal checkpoint fits reserved metadata blocks
media.kind == raw_nand  =>  controller BSP supplies channels, PHY, ECC, DMA, timing
offload.units marked `circuit` exist as @hw-tagged units in the firmware source
```

Overflow or truncation is a rejection, not a warning.

### 2.3 The no-hand-edit rule

**Generated files are never hand-edited.** Mechanically:

1. Every file in `generated/**` carries a first-line banner:
   `# GENERATED by simple nvme-profile-gen from <inputs>@<hash>. DO NOT EDIT.`
2. `generated/**` is committed (so builds are reproducible and diffs reviewable), and is listed in the workspace `FILE.md` manifest as generator-owned.
3. CI gate `scripts/check/check-nvme-profile-generated-clean.shs`: regenerate every board into a temp dir, `diff -r` against the committed tree. Any difference is FAIL, naming the files. Verdict convention per `.claude/rules/vcs.md`: `PASS — <n> file(s) regenerated and compared, 0 diffs` exit 0 / `FAIL — <n> file(s) differ: <names>` exit 1 / `ERROR — nothing was checked` exit 2. A run that regenerated 0 boards is ERROR, never a pass. `--selftest` runs first and is fatal.
4. A fix to generated output is a fix to the generator or the profile, never to the artifact.

---

## 3. Per-controller contracts

Evidence grades A–D and levels C0–C6 are the hardening plan's (§1, §3). "Ceiling" below is the **honest maximum reachable with what is publicly documented and procurable**, not a schedule.

### 3.1 `SimpleFpgaRv32` — in-repo, first profile

- **Supply:** RV32IMAC CPU block; the existing AXI/NVMe register map exported as SystemRDL (currently implicit in `.spl` source and RTL); single-page PRP; polling IRQ; queue depth 16, one I/O queue, `outstanding_max: 1`; PMP regions; `dram_model` or emulated-NAND media; offload profile with everything `firmware`.
- **Documented:** everything — it is ours. This is the only profile with no external unknowns.
- **Unavailable:** nothing; but it is not real media and not a real host.
- **Ceiling: C3.** RTL/co-simulation is reachable (GHDL firmware-in-loop exists). C4 needs a real host enumerating a real endpoint; C5 is impossible by construction (no NAND).
- **Role:** proves the generator produces buildable, linkable, simulating output. Migrating this profile off `TARGET_SIMPLE_SIM` is the first deliverable.

### 3.2 `CosmosPlusZynq7000` / `CosmosPlusReference` — first real-media target

- **Supply:** the example in §1.2, plus the BSP (ARM vector table, MMU/cache, SCU/GIC, FSBL handoff), the Tiger4NSC 8x8 NFC register/command binding, and the bitstream-hash identity contract.
- **Documented:** board schematics, Zynq-7000 TRM, upstream `Cosmos-plus-OpenSSD` PL project (v3.0.0 @ `78601486bb`), upstream register apertures and uProgROM command entries, `freshLiver/ocp-fw` cross-build pattern. Substantial prior work already in `cosmos_openssd_port_2026-06-30.md`.
- **Unavailable / hazardous:** NAND part datasheets are usually NDA — timing and read-retry tables may have to be derived from ONFI parameter pages plus measurement, and that provenance must be recorded. NFC commands are upstream ROM entries, **not** generic NAND opcodes, so the media profile cannot be assumed portable. Toolchain age (Vivado/Xilinx SDK era) threatens reproducibility. **Neither PL block has a trustworthy runtime identity register** — identity must be bound to the bitstream hash, which is a real fail-closed requirement, not a formality.
- **Ceiling: C5** with board + host + real NAND in hand; C6 additionally needs power-cut rigs, endurance time, and release gating. This is the **only** candidate whose ceiling reaches real-media HIL.

### 3.3 `OxDfcOpenChannel` — DFC / OX controller

- **Supply:** open-channel media profile (`kind: raw_nand`, host-managed), OX-style media-manager boundary, NVMe PCI / NVMe-oF transport descriptor.
- **Documented:** `DFC-OpenSource/ox-ctrl` is a complete, readable architecture — media manager / FTL / transport separation, DRAM/VOLT/file backends, BBT tasks, checkpoint/recovery. Its **architecture** is the most valuable thing in the survey.
- **Unavailable:** the DFC board (Broadcom Stingray) is effectively unobtainable; OX is Linux user-space with allocation and threading assumptions that must not enter the hard-real-time core.
- **Ceiling: C2** as a profile (its DRAM/file backends give a model-level target). Treat OX primarily as an **architectural precedent and differential oracle**, and be explicit that we are not claiming a DFC hardware profile.

### 3.4 `OpenExpressFrontend` and `NvmeChaFrontend` — OffloadProfile exemplars

These matter because queue fetch, PRP traversal, DMA and completion posting are **already in circuit**. They are the natural inverse of §1.2's offload file and the sharpest test that the offload axis is real.

- **Supply:** an `offload` profile with `queue_fetch/prp_walk/completion_post/dma_scatter: circuit`; a controller profile whose `mmio` describes the frontend's control/status registers; a media profile of `kind: block_backend` or `dram_model`; and a firmware-side contract stating which commands the software path still owns.
- **Documented:** OpenExpress — the USENIX ATC '20 paper describes the hardware-automated queue engine and reported near-PCIe-limit throughput; NVMeCHA — `yhqiu16/NVMeCHA` targets Xilinx KCU105, PCIe Gen3 x8, Vivado/Vitis 2019.2, one software-assisted admin controller plus per-queue-pair hardware I/O controllers.
- **Unavailable:** **neither is a NAND SSD.** Both back onto controller test memory or an external backend, so no FTL or media evidence flows from them. OpenExpress repository licensing is separate from paper availability and must be settled before any code is read for reuse (see §5); NVMeCHA is pinned to a 2019.2 toolchain and a specific board. No broad CI in either.
- **Ceiling: C4** (transport HIL — a host can enumerate the endpoint on the stated FPGA board) and **C5 is unreachable**: there is no real media behind them. Any claim above C4 for these profiles is a category error.

### 3.5 `LinuxPciEndpointReference` — ZCU106 / RK3588 / BeagleY-AI

- **Supply:** `transport: pcie_endpoint`; generated `devicetree.dtsi`; a `block_backend` media profile; a BSP that is a Linux PCI endpoint function rather than baremetal; explicitly `hard_realtime: false`.
- **Documented:** the NVMe-CSD project reports working on ZCU106, RK3399, RK3588 and BeagleY-AI/AM67A, extensible wherever a Linux PCI endpoint-controller driver exists; per-platform kernel/rootfs/device-tree build instructions exist. Boards are cheap and available (BeagleY-AI especially).
- **Unavailable:** intrinsic NAND — the backend is an arbitrary Linux block device. Endpoint-controller driver quality varies per SoC; DMA and doorbell semantics differ.
- **Ceiling: C4.** It is the **transport-portability reference**: it proves the host/NVMe layer is not welded to one controller. It is explicitly **not** evidence of real-NAND firmware portability, and the hardening plan says so.

### 3.6 Oracles, not products

`FemuDifferential`, `NvmeVirtDifferential`, and `HostReference` are profile-shaped so they run in the same matrix, but are flagged `role: oracle` in SDN and are rejected by the release gate if a production image ever links them. FEMU has real CI across three Ubuntu releases and multiple device modes; NVMeVirt gives independent host-visible behavior. Grade C evidence, permanently.

### 3.7 Summary

| Profile | Media reality | Ceiling | Why capped there |
|---|---|---|---|
| `SimpleFpgaRv32` | emulated | D3 | no real host, no NAND |
| `CosmosPlusReference` | real NAND | C5 (C6 with rigs) | only real-media candidate |
| `OxDfcOpenChannel` | open-channel / file | D2 | board unobtainable; user-space assumptions |
| `OpenExpressFrontend` | none (frontend) | D4 | no media behind it |
| `NvmeChaFrontend` | test memory | D4 | no media behind it |
| `LinuxPciEndpointReference` | block backend | D4 | not NAND, not hard-real-time |
| `HostReference` | model | D2 | oracle by definition |
| `Femu`/`NvmeVirt` | model | C2 (grade C) | oracle, never a product |

**Everything else is out of scope and must be said so.** Commercial controller register maps, NAND PHY interfaces, firmware ABIs, ROM protocols and secure-boot chains are private. "All controllers" in this plan means **certified documented profiles only** — a controller is supported when a complete profile, BSP, media profile and evidence bundle exist at a stated level, and not because the source compiles.

---

## 4. Portability acceptance test — mechanical

**The claim:** adding a controller requires ZERO edits to host/FTL/NAND core.

**The check:** `scripts/check/check-nvme-profile-core-untouched.shs BASE..NEW`

Mechanism, reading committed content via `git diff --name-only` (never the working copy):

1. Classify every changed path in the range:
   - **allowed:** `profiles/{controller,media,board,offload}/**`, `bsp/<new>/**`, `generated/<new-board>/**`, `test/**/profile_<new>*`, `doc/**`, the licensing ledger.
   - **core (forbidden):** `fw/ftl*`, `fw/fil*`, `fw/nvme_*`, `fw/hil*`, `fw/rain*`, `fw/rel_*`, `fw/nd_types*`, `src/os/drivers/nvme/**` — enumerated in `scripts/check/nvme_core_paths.txt`, not inferred.
2. A range whose allowed set contains a **new** `profiles/board/*.sdn` is a **profile-addition range**. For such a range, any touched core path is FAIL, naming the files.
3. Additionally: the pre-change core files must be **byte-identical** at both endpoints (`git cat-file` blob-id compare), so a whitespace-only or comment-only core edit is still a FAIL. This is the check that has teeth — a diff that "looks harmless" is exactly how the old `nvme_fw_target_config` if-chain would grow back.
4. Independently, `generated/<new-board>/**` must be reproducible (§2.3) — a hand-written "generated" file is a disguised core edit.

Verdict, last line of stdout: `PASS — <n> profile-addition range(s) checked, <k> core file(s) verified byte-identical` exit 0 / `FAIL — profile addition <board> touched core: <names>` exit 1 / `ERROR — nothing was checked` exit 2. A range with no board addition is not vacuously green: it reports 0 profile-addition ranges and exits **2**, so the caller must state that it checked nothing. **Scope:** this is therefore NOT a member of the always-on pre-push chain in `.claude/rules/vcs.md` — under that convention every ordinary push would ERROR. It is invoked by the profile contributor, and by a dispatcher that first greps the range for a new `profiles/board/*.sdn` and only then calls it. `--selftest` runs first and is fatal, with at least: a clean profile addition must PASS; the same addition plus a one-comment edit to `fw/ftl_map.spl` must FAIL naming that file; a hand-edited generated file must FAIL; an empty range must ERROR.

**Bootstrap fixture:** the first real run of this check is the `SimpleFpgaRv32`→`CosmosPlusReference` addition. If adding Cosmos+ requires core edits, the abstraction is wrong and the core must be fixed — not the check relaxed. There is no escape flag.

---

## 5. Licensing / source-origin ledger

**Rule: no external code, register description, timing table, or command sequence enters this tree until its origin has a ledger row.** The row is written and approved *before* the copy, not after. This is a hard gate on the profile-contribution contract (hardening §8.5 item 10).

Ledger: `doc/08_tracking/hardware/nvme_profile_source_origin.sdn`, table form:

```sdn
origins |id, profile, origin_url, upstream_rev, license, spdx, mode, target_paths, patent_notes, approver, approved_date, review_status|
    0, SimpleFpgaRv32, "in-repo", "", "repo-license", "", authored, "profiles/controller/simple_fpga_rv32.sdn", "", ormastes, 2026-09-01, approved
    1, CosmosPlusReference, "https://github.com/Cosmos-OpenSSD/Cosmos-plus-OpenSSD", "78601486bb5581e40628ec7e841dea8e97eff034", "TBD-verify", "", reimplemented, "profiles/controller/cosmos_plus_zynq7000.sdn", "PL bitstream redistribution unresolved", , , pending
```

Columns that carry the weight:

- **`mode`** — one of `authored` (ours), `reimplemented` (behavior derived from public docs, no source copied), `copied` (source vendored verbatim). `copied` requires the license text vendored alongside and an SPDX header on every file.
- **`review_status`** — `pending` blocks the build. The generator refuses to emit for a board any of whose origins is `pending` or `rejected`; the release gate refuses to package.
- **`patent_notes`** — hardware-automation designs and ECC schemes can carry patent exposure that a permissive source license does not clear.

Concrete reasons this rule is not ceremony:

- **OpenExpress:** the paper is openly available; the repository's licensing is a *separate* question and may forbid copying outright. Reading the paper to write a profile is `reimplemented`; lifting the Vivado sources is `copied` and may be impermissible. The ledger forces that distinction to be made explicitly and by name.
- **Cosmos+:** the upstream PL project ships a **bitstream** whose redistribution terms differ from its source terms — and our identity contract binds that bitstream's SHA-256, so we depend on it. Unresolved until a row says otherwise.
- **NVMeCHA / Lambda-IO / OX:** all readable, all with distinct upstream terms; OX in particular is a design we want to *learn from*, which is `reimplemented`, not `copied`.
- **FEMU / NVMeVirt:** oracles run as external processes and are **never linked**; their rows record that, so a future "just link it for convenience" is visibly a licensing change.

Ratchet: `scripts/check/check-profile-origin-ledger.shs` — every `profiles/**` and `bsp/**` directory maps to at least one `approved` row; every `copied` row's `target_paths` carry a matching SPDX header. Same verdict convention; 0 origins checked is ERROR.

---

## 6. Ordered deliverables

| # | Deliverable | Gate (certification level reached) |
|---|---|---|
| D1 | Schema + validator; `SimpleFpgaRv32` profile authored | profile parses, equations close (C0) |
| D2 | Generator emits the §2.1 output set; `check-nvme-profile-generated-clean.shs` green | C0 |
| D3 | `SimpleFpgaRv32` firmware builds from generated output; `TARGET_SIMPLE_SIM` and `nvme_fw_target_config`'s if-chain **deleted** from `openssd_config.spl` | C1 |
| D4 | `check-nvme-profile-core-untouched.shs` + selftests landed | gate exists before it is needed |
| D5 | `HostReference` + `Femu`/`NvmeVirt` oracle profiles | C2, differential matrix runs |
| D6 | Origin ledger + `check-profile-origin-ledger.shs`; all rows resolved | blocks D7 |
| D7 | `CosmosPlusReference` profile authored from the existing port plan; core-untouched check must PASS on this addition | C0→C1 |
| D8 | `LinuxPciEndpointReference` (BeagleY-AI, cheapest real host enumeration) | C4 ceiling |
| D9 | `OpenExpressFrontend`/`NvmeChaFrontend` offload profiles | C4 ceiling; proves the offload axis inverts with zero firmware edits |

D7 onward depends on hardware procurement, not on code.
