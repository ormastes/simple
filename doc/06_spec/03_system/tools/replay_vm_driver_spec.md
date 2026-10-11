# Replay VM Driver Specification

Status: **bounded Phase1 CPU-contract diagnostic passed**. The coordinator executed all 22 cases once: **22 passed, zero failed, zero skipped**, in **193 ms**, exit status **0**. No production implementation was changed and no runtime defect was demonstrated. This is a source-synchronized manual with admitted Phase1 seed diagnostic evidence, not generated docgen, native or full-VM qualification. Passing scenarios were not rerun.

Canonical source: `test/03_system/tools/replay_vm_driver_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`. Evidence class: **host-fixture**. The executed inventory comprises all **19 original scenarios and three additional CPU snapshot scenarios**. This is not a native binary inventory.

## Diagnostic evidence

Evidence root: `build/phase-one-storage-gui-diagnostic/`.
Execution log, resource receipt and exit status: `replay_vm_driver_spec/cycle-one.{log,rss.env,exit}`.
Input manifest: `vm-driver-cycle-one-inputs.sdn`; the coordinator verified all 13 recorded files before and after execution.

Canonical source SHA-256: `5866b45578c9e6674d8a422f6b7d0d35b9ce0745e1a250b32dfe77531189fe20`.
One diagnostic cycle was used. Convergence stops execution; the unused cycle budget is not a reason to rerun green checks.

## Contract and open obligations

Track 6 in `doc/07_guide/app/tools/sreplay.md` explicitly documents a CPU-register snapshot prototype. These checks exercise the real `VmReplayDriver`, its `Rv32iCpu`, and `VmConfig`/`VmState` owners under `src/lib/nogc_sync_mut/replay/vm/`. The three `@cover` percentages are targets, not measured coverage. No fake driver or replacement snapshot implementation is introduced.

Zero-byte memory keeps construction bounded and is adequate for the documented CPU register/PC/cycle contract. **OPEN:** memory contents, device state, CPU halted/pending-interrupt state, full-VM restoration, MMIO dispatch and replay-forward execution. The bus currently stores address descriptors, not live device instances. This spec does not close those obligations or establish device qualification. The known documented prototype limitations are not presented as dynamically reproduced bugs.

## Manual flow

1. Create the production driver, then assign distinct nonzero values to every writable register, PC and cycle counter. Check the populated fixture, including hardwired register x0.
2. Save through `save_snapshot`; change every writable register, PC and cycle counter; check the changed fixture before restoration.
3. Restore through `restore_snapshot`, require `Ok`, and compare every register, PC and cycle count with the saved values. Require the existing resumed `Running` driver behavior.
4. Save two snapshots with distinct CPU contents; mutate again; restore first, second, then first again. Each successful result must recover the corresponding full CPU contents, proving snapshots remain independent of later CPU mutation and restoration.
5. Populate the CPU and stop the driver. Request missing snapshot 999; require its error and prove that every register, PC, cycle count, stopped state, snapshot count and next snapshot ID remain unchanged.
6. Preserve all original configuration, creation, start, stepping, sequential ID, restore and run-step assertions.

Error branches fail explicitly; there are no source-substring acceptance checks. Production owners are unchanged at baseline: `replay_driver.spl` SHA-256 `07d87151232e2fab28f46fed1b03072ea78b965307b001fed72d7acf0927a7c9`, `vcpu.spl` SHA-256 `27233b622f6c3211ea578408d364c8fd0813413b4daa9fbbbc664a35428aaf48`.

Legacy `test/system/replay_vm_driver_spec.spl` was removed only after `tail -n +2` of the pre-edit canonical source compared byte-identically to it. The sole difference was canonical `@cover ... vm_types.spl 0%` metadata. Original canonical SHA-256: `6115cf409fda7ecc5c052b5aebf56c9cbf83e27363c0e0a14422a25e1a4a0d80`; original legacy SHA-256: `268aeeb372798cd0f5c70a672c15983c85d561b6bbb20b80b885396a1a1bd590`.

## Complete executable source

<details>
<summary>Executable SSpec, including setup and assertion helpers</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @tag:system
# @cover src/lib/nogc_sync_mut/replay/vm/vm_types.spl 80%
# @cover src/lib/nogc_sync_mut/replay/vm/replay_driver.spl 80%
# @cover src/lib/nogc_sync_mut/replay/vm/vcpu.spl 80%
# Coverage percentages are targets, not measured coverage.
# Evidence class: host-fixture; documented CPU register/PC/cycle prototype only.
# OPEN: memory bytes, live devices, halted/interrupt state and full-VM replay.
# System Tests — VM Replay Driver
#
# Tests for VmReplayDriver: construction, execution stepping,
# snapshot save/restore, and run_steps.
#
# Note: VirtualMemory.create allocates bytes one-by-one in interpreter mode.
# Use memory_mb=0 for driver tests to keep allocation instant (0 bytes).
# Memory read/write behaviour is covered in replay_rv32i_vm_spec.spl.

use std.spec
use std.nogc_sync_mut.replay.vm.vm_types.{VmConfig, VmState, VmReplayMode}
use std.nogc_sync_mut.replay.vm.replay_driver.{VmReplayDriver}

fn vm_snapshot_set_cpu_fixture(original: VmReplayDriver, register_base: i64, pc: i64, cycles: i64) -> VmReplayDriver:
    var driver = original
    driver.start(pc)
    driver.cpu.cycle_count = cycles
    var index = 0
    while index < 32:
        driver.cpu.write_register(index, register_base + index)
        index = index + 1
    driver

fn expect_vm_snapshot_cpu(driver: VmReplayDriver, register_base: i64, pc: i64, cycles: i64):
    expect(driver.get_pc()).to_equal(pc)
    expect(driver.get_cycle_count()).to_equal(cycles)
    expect(driver.read_register(0)).to_equal(0)
    var index = 1
    while index < 32:
        expect(driver.read_register(index)).to_equal(register_base + index)
        index = index + 1

# ============================================================================
# VmConfig — default_rv32
# ============================================================================

describe "VmConfig default_rv32":
    it "memory_mb matches requested value":
        val cfg = VmConfig.default_rv32(4)
        expect(cfg.memory_mb).to_equal(4)

    it "memory_mb is greater than zero":
        val cfg = VmConfig.default_rv32(4)
        expect(cfg.memory_mb).to_be_greater_than(0)

    it "num_cpus is 1":
        val cfg = VmConfig.default_rv32(4)
        expect(cfg.num_cpus).to_equal(1)

    it "devices list is non-empty":
        val cfg = VmConfig.default_rv32(4)
        val has_devices = cfg.devices.len() > 0
        expect(has_devices).to_equal(true)

# ============================================================================
# VmReplayDriver — create
# ============================================================================

describe "VmReplayDriver create":
    it "initial state is Stopped":
        # memory_mb=0 → 0-byte VirtualMemory, instant allocation
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        val is_stopped = driver.state == VmState.Stopped
        expect(is_stopped).to_equal(true)

    it "initial cycle_count is zero":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        expect(driver.get_cycle_count()).to_equal(0)

    it "initial pc is zero":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        expect(driver.get_pc()).to_equal(0)

# ============================================================================
# VmReplayDriver — start sets Running
# ============================================================================

describe "VmReplayDriver start sets Running":
    it "state is Running after start":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0)
        val is_running = driver.state == VmState.Running
        expect(is_running).to_equal(true)

    it "pc equals entry address after start":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0x1000)
        expect(driver.get_pc()).to_equal(0x1000)

# ============================================================================
# VmReplayDriver — step increments cycle
# ============================================================================

describe "VmReplayDriver step increments cycle":
    it "step on Stopped driver returns Stopped":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        # state is Stopped — step returns immediately
        val result = driver.step()
        val is_stopped = result == VmState.Stopped
        expect(is_stopped).to_equal(true)

    it "cycle_count is greater than zero after one step when Running":
        # With 0-byte memory, mem_read returns 0.
        # Instruction 0x00000000 has opcode 0x00 → unknown → halts.
        # CPU still increments cycle_count before returning Stopped.
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0)
        driver.step()
        expect(driver.get_cycle_count()).to_be_greater_than(0)

# ============================================================================
# VmReplayDriver — save_snapshot returns sequential ids
# ============================================================================

describe "VmReplayDriver save_snapshot returns sequential ids":
    it "first snapshot id is 0":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        val id = driver.save_snapshot()
        expect(id).to_equal(0)

    it "second snapshot id is 1":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.save_snapshot()
        val id2 = driver.save_snapshot()
        expect(id2).to_equal(1)

# ============================================================================
# VmReplayDriver — restore_snapshot
# ============================================================================

describe "VmReplayDriver restore_snapshot":
    it "restore_snapshot on valid id returns Ok":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0)
        val snap_id = driver.save_snapshot()
        val result = driver.restore_snapshot(snap_id)
        val is_ok = match result:
            case Ok(_): true
            case Err(_): false
        expect(is_ok).to_equal(true)

    it "restore_snapshot on missing id returns Err":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        val result = driver.restore_snapshot(999)
        val is_err = match result:
            case Ok(_): false
            case Err(_): true
        expect(is_err).to_equal(true)

    it "pc is restored to snapshot value":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0x100)
        val snap_id = driver.save_snapshot()
        # Change pc via start, then restore
        driver.start(0x200)
        driver.restore_snapshot(snap_id)
        expect(driver.get_pc()).to_equal(0x100)

# ============================================================================
# VmReplayDriver — complete documented CPU snapshot contract
# ============================================================================

describe "VmReplayDriver CPU snapshot contents":
    it "should restore every register PC and cycle count after mutation":
        step("Populate the production CPU with distinct nonzero register values")
        val config = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(config)
        driver = vm_snapshot_set_cpu_fixture(driver, 305397760, 4096, 12345)
        expect_vm_snapshot_cpu(driver, 305397760, 4096, 12345)
        val snapshot_id = driver.save_snapshot()
        step("Change every writable register PC and cycle count")
        driver = vm_snapshot_set_cpu_fixture(driver, 1450704896, 8192, 67890)
        expect_vm_snapshot_cpu(driver, 1450704896, 8192, 67890)
        step("Restore the snapshot and compare all CPU values")
        match driver.restore_snapshot(snapshot_id):
            case Ok(_):
                expect_vm_snapshot_cpu(driver, 305397760, 4096, 12345)
                expect(driver.state == VmState.Running).to_equal(true)
            case Err(message):
                fail("saved CPU snapshot could not be restored: {message}")

    it "should preserve independent CPU contents across two snapshots and repeated restores":
        step("Save two snapshots with different values in every writable CPU register")
        val config = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(config)
        driver = vm_snapshot_set_cpu_fixture(driver, 65536, 256, 100)
        val first_id = driver.save_snapshot()
        driver = vm_snapshot_set_cpu_fixture(driver, 131072, 512, 200)
        val second_id = driver.save_snapshot()
        expect(first_id).to_equal(0)
        expect(second_id).to_equal(1)
        driver = vm_snapshot_set_cpu_fixture(driver, 196608, 768, 300)
        step("Restore first then second then first again and compare the saved values")
        match driver.restore_snapshot(first_id):
            case Ok(_):
                expect_vm_snapshot_cpu(driver, 65536, 256, 100)
            case Err(message):
                fail("first CPU snapshot restore failed: {message}")
                return
        match driver.restore_snapshot(second_id):
            case Ok(_):
                expect_vm_snapshot_cpu(driver, 131072, 512, 200)
            case Err(message):
                fail("second CPU snapshot restore failed: {message}")
                return
        match driver.restore_snapshot(first_id):
            case Ok(_):
                expect_vm_snapshot_cpu(driver, 65536, 256, 100)
            case Err(message):
                fail("repeated first CPU snapshot restore failed: {message}")

    it "should reject a missing snapshot without changing registers PC cycles or stopped state":
        step("Set real CPU state and stop the driver before requesting a missing snapshot")
        val config = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(config)
        driver = vm_snapshot_set_cpu_fixture(driver, 262144, 1024, 400)
        driver.stop()
        expect_vm_snapshot_cpu(driver, 262144, 1024, 400)
        expect(driver.state == VmState.Stopped).to_equal(true)
        step("Require an error for the missing ID and compare all retained state")
        match driver.restore_snapshot(999):
            case Err(message):
                expect(message).to_contain("snapshot 999 not found")
                expect_vm_snapshot_cpu(driver, 262144, 1024, 400)
                expect(driver.state == VmState.Stopped).to_equal(true)
                expect(driver.snapshots.len()).to_equal(0)
                expect(driver.snapshot_counter).to_equal(0)
            case Ok(_):
                fail("missing snapshot unexpectedly restored")

# ============================================================================
# VmReplayDriver — run_steps
# ============================================================================

describe "VmReplayDriver run_steps":
    it "run_steps on Stopped driver stays Stopped":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        val result = driver.run_steps(5)
        val is_stopped = result == VmState.Stopped
        expect(is_stopped).to_equal(true)

    it "run_steps halts on unknown opcode from empty memory":
        # mem_read returns 0 → opcode 0x00 → unknown → halts after 1 cycle
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0)
        val result = driver.run_steps(100)
        val is_stopped = result == VmState.Stopped
        expect(is_stopped).to_equal(true)

    it "cycle_count is non-zero after run_steps with Running start":
        val cfg = VmConfig.default_rv32(0)
        var driver = VmReplayDriver.create(cfg)
        driver.start(0)
        driver.run_steps(5)
        expect(driver.get_cycle_count()).to_be_greater_than(0)
```

</details>
