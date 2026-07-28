# nvme_firmware_remaining_gates_spec

> Fail-closed orchestration for the remaining NVMe firmware production gates.
> Host software evidence never promotes unavailable UNO Q or Cosmos+ hardware.

| Field | Value |
|---|---|
| Source | `test/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.spl` |
| Runner | `scripts/check/check-nvme-firmware-remaining-gates.shs --self-test` |
| Package gate | `src/os/kernel/arch/arm32/cosmos/package_boot.shs --self-test` |

## Scenario

The runner verifies explicit simulator, QEMU, KV260, and OpenSSD profile
selection; rejects incomplete physical-board evidence; and executes package
manifest v3 provenance checks. The package gate requires complete compiled
source closure, a clean source revision, board serial/revision, boot mode,
compiler/linker/Bootgen identities, profile/contract/DMA values, and hashes for
FSBL, bitstream, firmware receipt/ELF, metadata, and `boot.bin`. Missing keys or
mismatched artifact hashes fail. The campaign gate additionally binds the six
BT result rows to retained raw logs, rejects path traversal and duplicate
metadata, and requires a reviewer different from the operator.

Expected software markers include:

```text
COSMOS_PACKAGE_PROVENANCE_PASS source=clean board=bound tools=clang,lld,bootgen
REJECTION missing-bt PASS
REJECTION tampered-log PASS
REJECTION path-traversal PASS
REJECTION duplicate-field PASS
REJECTION same-reviewer PASS
REJECTION package-source-mismatch PASS
STATUS: PASS nvme-firmware-remaining-gates self-test
STATUS: POSTPONED uno-q-supplementary environment-unavailable
STATUS: POSTPONED cosmos-board BT-001..BT-006
```

Physical BT-001..BT-006 acceptance remains separate and requires the identified
Cosmos+ board and retained raw campaign evidence.
