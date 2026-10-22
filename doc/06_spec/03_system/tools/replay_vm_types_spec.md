# Replay VM type contracts

Status: **10 PASS / 0 FAIL — non-admitting historical-seed diagnostic**. The coordinator executed this frozen canonical spec once: 863 ms, exit 0, peak RSS 235728 KiB, enforced limit 5859375 KiB, quiescent=1. Log, resource and exit receipts are under `build/phase-one-storage-gui-diagnostic/replay_vm_types_spec/cycle-one.*`; source/producer inputs are bound by `vm-types-cycle-one-inputs.sdn`. No passing case was rerun, and no production source or shared guide changed.

The exact retained seed SHA-256 is `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. Independent review verified all seven retained generation bindings, recorded in `/tmp/retained-phase1-seed-provenance-review-20261011.md` and the coordinator's `retained-generation-integrity-20261011.sdn`. The mutable marker `/tmp/beta-qual-4159b0b6/src/compiler_rust/target/bootstrap.current.env` and preflight `/tmp/beta-qual-4159b0b6/.simple/storage/build/bootstrap/bootstrap-preflight.env` are absent. Retained artifact identity supports this historical diagnostic provenance; it does not establish current Phase1 admission or fresh preflight. Resource containment receipts are not compiler-admission receipts. No marker/preflight was recreated.

This result is **not currently admitted Phase1, normal self-hosted/fullCLI, native, whole-suite or release qualification**. The diagnostic passed and is complete; it must not be rerun merely to obtain another green receipt.

## Actual behavior and dependencies

The seven original cases remain intact. New cases check every field of the two default UART/timer mappings, both previously unchecked replay-mode names and the remaining three device-I/O discriminants. The device array is length-checked before indexed access. These assertions inspect actual constructor/method results; no source-text checks or guest execution are used.

Production owner: `src/lib/nogc_sync_mut/replay/vm/vm_types.spl` (SHA-256 `aa3c28a1e9aaad7c2b75063f53cb2476a851ae2dcd142478ea0d3c56a2e7cc18`). `vm_types.spl` imports `std.nogc_sync_mut.replay.types.{Arch}`; `types.spl` has no imports. The spec also directly imports that Arch module and `std.spec`. These are direct production dependencies; the coordinator's frozen execution manifest must also bind the actual shared harness and producer closure.

No guest, QEMU, MMIO operation, device execution, CPU/memory replay, snapshot correctness or native runtime is exercised. No production defect was established by this bounded static intake. A baseline failure must be recorded and scoped before authorizing a source fix.

## Evidence and admission limits

Requirement trace: `REQ-SSPEC-SYSTEM`. Coverage 80% is an admission target, not measured coverage. The canonical source has real assertions and visible steps; this manual is synchronized directly to it, while SPipe docgen remains pending. No normal self-hosted/native, full-Phase1 or release qualification is claimed. The historical seed provenance and missing current-authority pointers are explicitly recorded above.

The original canonical and legacy `test/system/replay_vm_types_spec.spl` were fully byte-identical, SHA-256 `c9aba615f596f69cc09ac42705dc12bf9f2f835d6b4ed9e25a566f368af56871`. The duplicate was removed after preserving every original case; neither original header carried an additional requirement or tag. Bounded searches found no explicit legacy-path references in scripts, app source or system-test plans. Other lanes were not modified.

Canonical SHA-256: `ef2a89729bbc0a9d8d66307d8101d925a9d8e940db481f7eafdae2f3a1976dae`. Preparation metadata: `build/phase-one-storage-gui-diagnostic/replay-type-contracts-prepared.sdn`. The first and only baseline executed this complete canonical file once. All cases passed; no further runtime execution is planned.

## Scenarios and visible steps

Every scenario contains a visible `step(...)` describing its operation. Detailed assertions appear in the exact executable source below.

| Case | Scenario | Evidence |
|---|---|---|
| 1 | default_rv32 sets arch to RISCV32 | Diagnostic PASS |
| 2 | default_rv32 sets memory_mb correctly | Diagnostic PASS |
| 3 | default_rv32 sets num_cpus to 1 | Diagnostic PASS |
| 4 | default_rv32 replay_mode is Live | Diagnostic PASS |
| 5 | VmReplayMode Record to_text returns record | Diagnostic PASS |
| 6 | DeviceIoKind MmioRead to_i32 returns 0 | Diagnostic PASS |
| 7 | DeviceIoKind Interrupt to_i32 returns 2 | Diagnostic PASS |
| 8 | default_rv32 supplies the complete UART and timer map | Diagnostic PASS |
| 9 | names the replay and snapshot modes distinctly | Diagnostic PASS |
| 10 | preserves the remaining device I/O discriminants | Diagnostic PASS |

<details>
<summary>Exact executable SSpec source</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/nogc_sync_mut/replay/vm/vm_types.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# @tag:system
# Pure configuration/type contracts; no guest, device execution or native qualification.

use std.spec.{describe, it, expect, step}
use std.nogc_sync_mut.replay.types.{Arch}
use std.nogc_sync_mut.replay.vm.vm_types.{VmConfig, VmState, VmReplayMode, DeviceConfig, DeviceIoKind}

describe "VmConfig default_rv32":
    it "default_rv32 sets arch to RISCV32":
        step("default_rv32 sets arch to RISCV32")
        val cfg = VmConfig.default_rv32(128)
        val at = cfg.arch.to_text()
        expect(at).to_equal("riscv32")

    it "default_rv32 sets memory_mb correctly":
        step("default_rv32 sets memory_mb correctly")
        val cfg = VmConfig.default_rv32(256)
        expect(cfg.memory_mb).to_equal(256)

    it "default_rv32 sets num_cpus to 1":
        step("default_rv32 sets num_cpus to 1")
        val cfg = VmConfig.default_rv32(64)
        expect(cfg.num_cpus).to_equal(1)

    it "default_rv32 replay_mode is Live":
        step("default_rv32 replay_mode is Live")
        val cfg = VmConfig.default_rv32(64)
        val mt = cfg.replay_mode.to_text()
        expect(mt).to_equal("live")

    it "VmReplayMode Record to_text returns record":
        step("VmReplayMode Record to_text returns record")
        val m = VmReplayMode.Record
        expect(m.to_text()).to_equal("record")

    it "DeviceIoKind MmioRead to_i32 returns 0":
        step("DeviceIoKind MmioRead to_i32 returns 0")
        val k = DeviceIoKind.MmioRead
        expect(k.to_i32()).to_equal(0)

    it "DeviceIoKind Interrupt to_i32 returns 2":
        step("DeviceIoKind Interrupt to_i32 returns 2")
        val k = DeviceIoKind.Interrupt
        expect(k.to_i32()).to_equal(2)

describe "VM default device map and remaining enum contracts":
    it "default_rv32 supplies the complete UART and timer map":
        step("Construct the production RV32 configuration and inspect both devices")
        val cfg = VmConfig.default_rv32(128)
        expect(cfg.devices.len()).to_equal(2)
        if cfg.devices.len() == 2:
            val uart = cfg.devices[0]
            expect(uart.name).to_equal("uart0")
            expect(uart.base_addr).to_equal(0x10000000)
            expect(uart.size).to_equal(0x100)
            expect(uart.irq).to_equal(10)
            val timer = cfg.devices[1]
            expect(timer.name).to_equal("timer0")
            expect(timer.base_addr).to_equal(0x02000000)
            expect(timer.size).to_equal(0x10000)
            expect(timer.irq).to_equal(7)

    it "names the replay and snapshot modes distinctly":
        step("Convert the remaining production replay modes to their public names")
        expect(VmReplayMode.Replay.to_text()).to_equal("replay")
        expect(VmReplayMode.Snapshot.to_text()).to_equal("snapshot")

    it "preserves the remaining device I/O discriminants":
        step("Inspect the production write, DMA and timer event identifiers")
        expect(DeviceIoKind.MmioWrite.to_i32()).to_equal(1)
        expect(DeviceIoKind.DmaTransfer.to_i32()).to_equal(3)
        expect(DeviceIoKind.TimerFired.to_i32()).to_equal(4)
```

</details>
