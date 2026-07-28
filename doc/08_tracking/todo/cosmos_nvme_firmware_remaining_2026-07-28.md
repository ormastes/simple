# Cosmos NVMe Firmware Remaining Work

These items are deliberately separate from completed host/ARM contract work.
Postponed hardware rows remain open and must not be converted into host PASS.

# TODO: [cosmos][P0] Produce a source-matched pure-Simple runner, then execute ST-018 and regenerate the Cosmos SSpec manual.
# TODO: [nvme][P0] Implement fail-closed multi-target firmware profiles for Simple simulation, QEMU/FEMU, Cosmos OpenSSD, and KV260/FPGA without silently mapping unknown hardware to the simulator.
# TODO: [cosmos][P1] Complete package-manifest provenance for repository revision, dirty state, tool versions, bound profile, board identity, and immutable artifact hashes.
# TODO: [uno_q][P2] POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance.
# TODO: [cosmos][P0] POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006.

## Resume Order

1. Admit a current pure-Simple runtime and run the post-bootstrap host gate.
2. Implement and exercise the requested multi-target selector and capability
   matrix.
3. Complete package provenance and pin the exact board package.
4. Run the optional UNO Q portability lane when its environment exists.
5. Run BT-001..BT-006 only on the identified Cosmos+ board.

The canonical wrapper is
`scripts/check/check-nvme-firmware-remaining-gates.shs`. Its host result and
external-board result are intentionally separate.
