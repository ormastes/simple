# nvme_cosmos_openssd_boot_spec

> Verifies the nvme cosmos openssd boot behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_cosmos_openssd_boot_spec

Verifies the nvme cosmos openssd boot behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/cosmos_openssd_production_hal.md |
| Plan | doc/03_plan/sys_test/cosmos_openssd_production_hal.md |
| Design | doc/05_design/cosmos_openssd_production_hal.md |
| Source | `test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the nvme cosmos openssd boot behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Cosmos+ OpenSSD production HAL

#### should execute the host FSBL, NFC, and PCIe MMIO state machines

- Verify: should execute the host FSBL, NFC, and PCIe MMIO state machines
- Compile and run the fail-closed host mock-MMIO integration driver
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Verify all six bounded MMIO scenarios complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012 REQ-001..004 REQ-003..004 REQ-006..007 REQ-008..009 REQ-004..005 REQ-010..011
step("Verify: should execute the host FSBL, NFC, and PCIe MMIO state machines")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Compile and run the fail-closed host mock-MMIO integration driver")
val (out, err, code) = _run("sh " + HOST_MMIO)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

step("Verify all six bounded MMIO scenarios complete")
expect(out).to_contain("PASS FSBL handoff and PCFG_DONE")
expect(out).to_contain("PASS unconfigured PL fail-closed")
expect(out).to_contain("PASS NFC bounded initialization")
expect(out).to_contain("PASS NFC read/program/erase/ECC")
expect(out).to_contain("PASS NFC timeout quarantine")
expect(out).to_contain("PASS PCIe link/function/MSI/admin")
expect(out).to_contain("STATUS: PASS cosmos host mock-MMIO integration")
_expect_no_fail(out, err, "Cosmos host mock-MMIO integration")
```

</details>

#### should execute the standalone PCIe contract runner

- Verify: should execute the standalone PCIe contract runner
- Compile and run the bounded PCIe controller contract driver
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: auto_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-009 REQ-010 REQ-012
step("Verify: should execute the standalone PCIe contract runner")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Compile and run the bounded PCIe controller contract driver")
val (out, err, code) = _run("sh " + HOST_PCIE)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos PCIe contract: PASS")
_expect_no_fail(out, err, "Cosmos PCIe contract")
val (auto_out, auto_err, auto_code) = _run(
    "sh " + HOST_PCIE_AUTO_COMPLETION
)
expect(auto_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(auto_out).to_contain(
    "cosmos PCIe AUTO completion contract: PASS"
)
expect(auto_out).to_contain(
    "cosmos PCIe AUTO completion ARM compile: PASS"
)
_expect_no_fail(auto_out, auto_err, "Cosmos PCIe AUTO completion")
```

</details>

#### should execute actual ARM prefetch and data abort entry paths

- Verify: should execute actual ARM prefetch and data abort entry paths
- Run bounded QEMU injections through the production ARM vectors
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should execute actual ARM prefetch and data abort entry paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run bounded QEMU injections through the production ARM vectors")
val (out, err, code) = _run("sh " + HOST_ABORT)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("prefetch: PASS")
expect(out).to_contain("data: PASS")
expect(out).to_contain("cosmos ARM prefetch/data abort contract: PASS")
_expect_no_fail(out, err, "Cosmos ARM abort contract")
```

</details>

#### should execute the hardened NVMe IO callback service contract runner

- Verify: should execute the hardened NVMe IO callback service contract runner
- Run bounded IO validation, identity, DMA-span, and publication tests
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should execute the hardened NVMe IO callback service contract runner")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run bounded IO validation, identity, DMA-span, and publication tests")
val (out, err, code) = _run("sh " + HOST_NVME)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos NVMe firmware contract: PASS")
expect(out).to_contain("cosmos NVMe firmware ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe callback service contract")
```

</details>

#### should execute the crash-consistent FTL metadata contract runner

- Verify: should execute the crash-consistent FTL metadata contract runner
- Run PPA, journal, checkpoint, recovery, retirement, and fail-closed checks
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: gc_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: discard_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: journal_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: trim_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tx_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should execute the crash-consistent FTL metadata contract runner")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run PPA, journal, checkpoint, recovery, retirement, and fail-closed checks")
val (out, err, code) = _run("sh " + HOST_FTL)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos FTL contract: PASS")
expect(out).to_contain("cosmos FTL ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos FTL metadata contract")
val (gc_out, gc_err, gc_code) = _run("sh " + HOST_FTL_GC)
expect(gc_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(gc_out).to_contain("cosmos FTL GC contract: PASS")
expect(gc_out).to_contain("cosmos FTL GC ARM compile: PASS")
_expect_no_fail(gc_out, gc_err, "Cosmos FTL GC contract")
val (discard_out, discard_err, discard_code) = _run(
    "sh " + HOST_FTL_DISCARD
)
expect(discard_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(discard_out).to_contain("cosmos FTL discard contract: PASS")
expect(discard_out).to_contain(
    "cosmos FTL discard ARM compile: PASS"
)
_expect_no_fail(discard_out, discard_err, "Cosmos FTL discard")
val (journal_out, journal_err, journal_code) = _run(
    "sh " + HOST_FTL_JOURNAL
)
expect(journal_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(journal_out).to_contain(
    "cosmos FTL journal reclaim contract: PASS"
)
expect(journal_out).to_contain(
    "cosmos FTL journal reclaim ARM compile: PASS"
)
_expect_no_fail(journal_out, journal_err, "Cosmos FTL journal reclaim")
val (trim_out, trim_err, trim_code) = _run(
    "sh " + HOST_FTL_RECOVERY_TRIM
)
expect(trim_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(trim_out).to_contain(
    "cosmos FTL recovery trim contract: PASS"
)
expect(trim_out).to_contain(
    "cosmos FTL recovery trim ARM compile: PASS"
)
_expect_no_fail(trim_out, trim_err, "Cosmos FTL recovery trim")
val (tx_out, tx_err, tx_code) = _run(
    "sh " + HOST_FTL_TRANSACTION
)
expect(tx_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tx_out).to_contain(
    "cosmos FTL transaction recovery contract: PASS"
)
expect(tx_out).to_contain(
    "cosmos FTL transaction recovery ARM compile: PASS"
)
_expect_no_fail(tx_out, tx_err, "Cosmos FTL transaction recovery")
```

</details>

#### should bind persistent NFC media and fail closed outside silicon

- Verify: should bind persistent NFC media and fail closed outside silicon
- Run NFC wire-format, media staging, and startup composition checks
   - Expected: nfc_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: nfc_io_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: nfc_dma_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: media_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: physical_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tag_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: refresh_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: refresh_build_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: startup_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: link_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 118 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should bind persistent NFC media and fail closed outside silicon")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run NFC wire-format, media staging, and startup composition checks")
val (nfc_out, nfc_err, nfc_code) = _run("sh " + HOST_FTL_NFC)
expect(nfc_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(nfc_out).to_contain(
    "cosmos FTL NFC persistence backend: PASS"
)
expect(nfc_out).to_contain(
    "cosmos FTL NFC persistence backend ARM compile: PASS"
)
_expect_no_fail(nfc_out, nfc_err, "Cosmos FTL NFC persistence")
val (nfc_io_out, nfc_io_err, nfc_io_code) = _run(
    "sh " + HOST_FTL_NFC_IO
)
expect(nfc_io_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(nfc_io_out).to_contain(
    "cosmos FTL NFC IO fail-closed: PASS"
)
expect(nfc_io_out).to_contain(
    "cosmos FTL NFC IO fail-closed ARM compile: PASS"
)
_expect_no_fail(nfc_io_out, nfc_io_err, "Cosmos FTL NFC IO")
val (nfc_dma_out, nfc_dma_err, nfc_dma_code) = _run(
    "sh " + HOST_FTL_NFC_DMA
)
expect(nfc_dma_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(nfc_dma_out).to_contain(
    "cosmos FTL NFC metadata/payload DMA isolation: PASS"
)
expect(nfc_dma_out).to_contain(
    "cosmos FTL NFC metadata/payload DMA isolation ARM compile: PASS"
)
_expect_no_fail(nfc_dma_out, nfc_dma_err, "Cosmos FTL NFC DMA")

val (media_out, media_err, media_code) = _run(
    "sh " + HOST_FTL_MEDIA
)
expect(media_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(media_out).to_contain(
    "cosmos NVMe FTL media adapter: PASS"
)
expect(media_out).to_contain(
    "cosmos NVMe FTL media adapter ARM compile: PASS"
)
_expect_no_fail(media_out, media_err, "Cosmos NVMe FTL media")

val (physical_out, physical_err, physical_code) = _run(
    "sh " + HOST_FTL_PHYSICAL
)
expect(physical_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(physical_out).to_contain(
    "cosmos NVMe physical media composition: PASS"
)
expect(physical_out).to_contain(
    "cosmos NVMe physical media composition ARM compile: PASS"
)
_expect_no_fail(
    physical_out, physical_err, "Cosmos NVMe physical composition"
)

val (tag_out, tag_err, tag_code) = _run("sh " + HOST_FTL_TAG)
expect(tag_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tag_out).to_contain(
    "cosmos NVMe media page-tag validation: PASS"
)
expect(tag_out).to_contain(
    "cosmos NVMe media page-tag validation ARM compile: PASS"
)
_expect_no_fail(tag_out, tag_err, "Cosmos NVMe page tag")

val (refresh_out, refresh_err, refresh_code) = _run(
    "sh " + HOST_FTL_ECC_REFRESH
)
expect(refresh_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(refresh_out).to_contain(
    "cosmos NVMe ECC refresh relocation: PASS"
)
expect(refresh_out).to_contain(
    "cosmos NVMe ECC refresh relocation ARM compile: PASS"
)
_expect_no_fail(refresh_out, refresh_err, "Cosmos NVMe ECC refresh")

val (refresh_build_out, refresh_build_err, refresh_build_code) = _run(
    "sh " + HOST_FTL_ECC_BUILD
)
expect(refresh_build_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(refresh_build_out).to_contain(
    "cosmos ECC refresh API and ARM relocatable link: PASS"
)
_expect_no_fail(
    refresh_build_out, refresh_build_err, "Cosmos ECC refresh build"
)

val (startup_out, startup_err, startup_code) = _run(
    "sh " + HOST_STORAGE_STARTUP
)
expect(startup_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(startup_out).to_contain(
    "cosmos storage QEMU fail-closed startup: PASS"
)
expect(startup_out).to_contain(
    "cosmos storage startup ARM profiles compile: PASS"
)
_expect_no_fail(startup_out, startup_err, "Cosmos storage startup")

val (link_out, link_err, link_code) = _run(
    "sh " + HOST_STORAGE_LINK
)
expect(link_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(link_out).to_contain(
    "cosmos storage qemu production link: PASS"
)
expect(link_out).to_contain(
    "cosmos storage silicon production link: PASS"
)
_expect_no_fail(link_out, link_err, "Cosmos storage production link")
```

</details>

#### should execute the PCIe-to-NVMe bridge contract runner

- Verify: should execute the PCIe-to-NVMe bridge contract runner
- Run DW0/DW1/DW6-DW12, AUTO-DMA PRP, and completion transport checks
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: prp_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should execute the PCIe-to-NVMe bridge contract runner")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run DW0/DW1/DW6-DW12, AUTO-DMA PRP, and completion transport checks")
val (out, err, code) = _run("sh " + HOST_NVME_ADAPTER)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos NVMe PCIe adapter contract: PASS")
expect(out).to_contain("cosmos NVMe PCIe adapter ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe PCIe adapter contract")
val (prp_out, prp_err, prp_code) = _run(
    "sh " + HOST_NVME_PRP_CONTROL
)
expect(prp_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(prp_out).to_contain("cosmos NVMe PRP/control contract: PASS")
expect(prp_out).to_contain("cosmos NVMe FUA/LR contract: PASS")
expect(prp_out).to_contain(
    "cosmos NVMe PRP/control ARM compile: PASS"
)
_expect_no_fail(prp_out, prp_err, "Cosmos NVMe PRP/control")
```

</details>

#### should execute the NVMe admin callback core contract runner

- Verify: should execute the NVMe admin callback core contract runner
- Run corrected bounded Identify, SMART, queue, feature, Abort, and AER checks
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should execute the NVMe admin callback core contract runner")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run corrected bounded Identify, SMART, queue, feature, Abort, and AER checks")
val (out, err, code) = _run("sh " + HOST_NVME_ADMIN)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos NVMe admin contract: PASS")
expect(out).to_contain("cosmos NVMe admin ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe admin contract")
```

</details>

#### should route the single PCIe command FIFO to admin or IO exactly once

- Verify: should route the single PCIe command FIFO to admin or IO exactly once
- Run queue-zero admin, IO, retry, terminal, and reserved-field routing checks
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should route the single PCIe command FIFO to admin or IO exactly once")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run queue-zero admin, IO, retry, terminal, and reserved-field routing checks")
val (out, err, code) = _run("sh " + HOST_NVME_DISPATCH)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos NVMe dispatcher contract: PASS")
expect(out).to_contain("cosmos NVMe dispatcher ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe dispatcher contract")
```

</details>

#### should execute the host SMP, GIC, MMU, and cache contracts

- Verify: should execute the host SMP, GIC, MMU, and cache contracts
- Compile and run the host SMP/cache contract driver
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Verify cache operands, coherency ordering, GIC limits, and CPU1 protocol


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-006 REQ-007 REQ-009 REQ-010 REQ-012
step("Verify: should execute the host SMP, GIC, MMU, and cache contracts")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Compile and run the host SMP/cache contract driver")
val (out, err, code) = _run("sh " + HOST_SMP_CACHE)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

step("Verify cache operands, coherency ordering, GIC limits, and CPU1 protocol")
expect(out).to_contain("STATUS: PASS cosmos SMP/cache contract")
_expect_no_fail(out, err, "Cosmos host SMP/cache contract")
```

</details>

#### should boot the unbound QEMU image with an exact software-only verdict

- Verify: should boot the unbound QEMU image with an exact software-only verdict
- Build every Cosmos HAL unit and boot the Zynq QEMU machine
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Verify the hardware-independent runtime, MMU/cache, and GIC statuses
- Verify every board-only lane remains explicitly unavailable
- Keep physical production acceptance pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002 REQ-003 REQ-005 REQ-006 REQ-007 REQ-008 REQ-010 REQ-012
step("Verify: should boot the unbound QEMU image with an exact software-only verdict")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Build every Cosmos HAL unit and boot the Zynq QEMU machine")
val (out, err, code) = _run("COSMOS_BUILD_MODE=qemu sh " + BUILD + " --run")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain(
    "built build/os/simpleos_cosmos_openssd.elf (clean, unbound, entry="
)
expect(out).to_contain("COSMOS+ OpenSSD (Zynq-7000 / Cortex-A9) boot OK")

step("Verify the hardware-independent runtime, MMU/cache, and GIC statuses")
expect(out).to_contain("[cosmos] ARMv7 runtime: OK")
expect(out).to_contain("[cosmos] MMU/L1/PL310: OK")
expect(out).to_contain("[cosmos] GIC primary: OK")

step("Verify every board-only lane remains explicitly unavailable")
expect(out).to_contain("[cosmos] CPU1 release: UNAVAILABLE")
expect(out).to_contain("[cosmos] FSBL handoff: UNAVAILABLE")
expect(out).to_contain("[cosmos] NFC PL: UNAVAILABLE")
expect(out).to_contain("[cosmos] PCIe PL: UNAVAILABLE")

step("Keep physical production acceptance pending")
expect(out).to_contain("COSMOS SOFTWARE HAL CHECKS PASS")
expect(out).to_contain("COSMOS SILICON VALIDATION PENDING")
_expect_absent(out, "COSMOS SILICON HAL CHECKS PASS", "Cosmos QEMU profile")
_expect_no_fail(out, err, "Cosmos QEMU profile")
```

</details>

#### should build and identify the exact bound silicon profile

- Verify: should build and identify the exact bound silicon profile
- Build the silicon image with the exact reviewed profile selector
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Inspect ELF type, loadability, profile note, exact symbol, and link closure
   - Expected: elf_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-011 REQ-012
step("Verify: should build and identify the exact bound silicon profile")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Build the silicon image with the exact reviewed profile selector")
val command = "COSMOS_BUILD_MODE=silicon COSMOS_SILICON_PROFILE=" + PROFILE +
    " sh " + BUILD
val (out, err, code) = _run(command)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain(
    "built " + SILICON_ELF + " (clean, profile=" + PROFILE + ", entry="
)
_expect_no_fail(out, err, "Cosmos bound silicon build")

step("Inspect ELF type, loadability, profile note, exact symbol, and link closure")
val inspect = "readelf -hW " + SILICON_ELF +
    " && readelf -lW " + SILICON_ELF +
    " && readelf -SW " + SILICON_ELF +
    " && readelf -sW " + SILICON_ELF +
    " && readelf -p .note.cosmos.profile " + SILICON_ELF +
    " && test -z \"$(nm -u " + SILICON_ELF + ")\""
val (elf_out, elf_err, elf_code) = _run(inspect)
expect(elf_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(elf_out).to_contain("ELF32")
expect(elf_out).to_contain("EXEC")
expect(elf_out).to_contain("ARM")
expect(elf_out).to_contain("LOAD")
expect(elf_out).to_contain(".note.cosmos.profile")
expect(elf_out).to_contain(PROFILE_SYMBOL)
expect(elf_out).to_contain("profile=cosmos-plus-" + PROFILE)
expect(elf_out).to_contain("source=78601486bb5581e40628ec7e841dea8e97eff034")
expect(elf_out).to_contain("bitstream=66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2")
_expect_no_fail(elf_out, elf_err, "Cosmos silicon ELF inspection")
```

</details>

#### should reject invalid boot inputs and publish bound package metadata

- Verify: should reject invalid boot inputs and publish bound package metadata
- Run ELF, bitstream, alias, Bootgen metadata, hash, and manifest checks
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-012
step("Verify: should reject invalid boot inputs and publish bound package metadata")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run ELF, bitstream, alias, Bootgen metadata, hash, and manifest checks")
val (out, err, code) = _run("sh " + PACKAGE + " --self-test")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("COSMOS_PACKAGE_PROVENANCE_PASS source=clean board=bound tools=clang,lld,bootgen")
expect(out).to_contain("STATUS: PASS cosmos-package-boot self-test")
_expect_no_fail(out, err, "Cosmos package self-test")
```

</details>

#### should retain ARM EABI division edges and runtime self-test markers

- Verify: should retain ARM EABI division edges and runtime self-test markers
- Run host behavior and unresolved-symbol checks for the ARM runtime ABI
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Inspect the freestanding runtime ABI and divide-by-zero hook
- Bind those edge checks to the boot-time runtime verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010 REQ-011 REQ-012
step("Verify: should retain ARM EABI division edges and runtime self-test markers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Run host behavior and unresolved-symbol checks for the ARM runtime ABI")
val (out, err, code) = _run("sh " + HOST_RUNTIME)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("cosmos runtime contract: PASS")
expect(out).to_contain("cosmos runtime host/ARM ABI objects: PASS")
_expect_no_fail(out, err, "Cosmos runtime ABI contract")

step("Inspect the freestanding runtime ABI and divide-by-zero hook")
val runtime = file_read_text("src/os/kernel/arch/arm32/cosmos/cosmos_runtime.c")
expect(runtime).to_contain("__attribute__((weak)) int __aeabi_idiv0")
expect(runtime).to_contain("result = __aeabi_uidivmod(unsigned_max, unsigned_max);")
expect(runtime).to_contain("__aeabi_uidiv(unsigned_max, 2U) != 0x7FFFFFFFU")
expect(runtime).to_contain("__aeabi_idiv(signed_min, -1) != signed_min")
expect(runtime).to_contain("cosmos_udivmod(1U, 0U, &quotient, &remainder) != 0")
expect(runtime).to_contain("__aeabi_idiv0(123) != 123")
expect(runtime).to_contain("(cosmos_u64)remainder << 32")

step("Bind those edge checks to the boot-time runtime verdict")
val boot = file_read_text("src/os/kernel/arch/arm32/cosmos/cosmos_uart.c")
expect(boot).to_contain("runtime_status = cosmos_runtime_selftest();")
expect(boot).to_contain("cosmos_report_status(\"ARMv7 runtime\", runtime_status);")
expect(boot).to_contain("runtime_status == COSMOS_OK")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/cosmos_openssd_production_hal.md`
- **Plan:** `doc/03_plan/sys_test/cosmos_openssd_production_hal.md`
- **Design:** `doc/05_design/cosmos_openssd_production_hal.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `787b546a04b4bfa1a02b940c9fce2ddcc801c5136bd42e119ae055c6ef781d54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `787b546a04b4bfa1a02b940c9fce2ddcc801c5136bd42e119ae055c6ef781d54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `787b546a04b4bfa1a02b940c9fce2ddcc801c5136bd42e119ae055c6ef781d54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the host FSBL, NFC, and PCIe MMIO state machines' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the standalone PCIe contract runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:160:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute actual ARM prefetch and data abort entry paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:173:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the hardened NVMe IO callback service contract runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:185:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the crash-consistent FTL metadata contract runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:244:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind persistent NFC media and fail closed outside silicon' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
