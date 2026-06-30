# nvme_firmware_simulation_spec

> NVMe SSD firmware (HIL/FTL/FIL + admin/IO-queue controller) — system scenario.

<!-- sdn-diagram:id=nvme_firmware_simulation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_firmware_simulation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_firmware_simulation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_firmware_simulation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_firmware_simulation_spec

NVMe SSD firmware (HIL/FTL/FIL + admin/IO-queue controller) — system scenario.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-FW-001 |
| Category | Hardware |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_firmware_simulation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe SSD firmware (HIL/FTL/FIL + admin/IO-queue controller) — system scenario.

The pure-Simple firmware (examples/09_embedded/simpleos_nvme_fw/fw/) is a layered,
host-runnable NVMe SSD controller simulation: a Host Interface Layer (queues +
command decode), a Flash Translation Layer (log-structured map, WAL/checkpoint,
crash recovery, garbage collection), a Flash Interface Layer (ONFI NAND device +
ECC + bad-block), and an NVMe controller front end (admin queue + multiple IO
queues). The modules live under examples/ and are exercised here through the real
CLI (`bin/simple run`) as subprocesses, asserting the operator-visible PASS
evidence. Run: `bin/simple test test/03_system/app/nvme_firmware/nvme_firmware_simulation_spec.spl`.

## Scenarios

### NVMe firmware: layered self-tests (HIL / FTL / FIL + controller)

#### passes the full firmware self-test suite

- Run the aggregated firmware self-test suite
   - Expected: code equals `0`
- Confirm each layer's section ran
- Confirm the suite reports overall PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the aggregated firmware self-test suite")
val (out, err, code) = _run(FW + "/test_fw.spl")
expect(code).to_equal(0)

step("Confirm each layer's section ran")
expect(out).to_contain("FIL (flash interface)")
expect(out).to_contain("FTL (translation)")
expect(out).to_contain("HIL (host interface)")
expect(out).to_contain("NVMe controller (admin + multi IO queue)")

step("Confirm the suite reports overall PASS")
expect(out).to_contain("ALL FIRMWARE SELF-TESTS PASS")
```

</details>

### NVMe firmware: end-to-end SSD lifecycle

#### writes, reads, garbage-collects, trims, and survives a power cycle

- Run the end-to-end SSD simulation
   - Expected: code equals `0`
- Read-back verification after the initial writes
- Overwrites produce stale pages and the newest version reads back
- Garbage collection reclaims a stale block while the logical view is preserved
- Trim deallocates an LBA (a later read returns zero)
- After a power-fail + recovery, committed data survives and trims stay trimmed


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the end-to-end SSD simulation")
val (out, err, code) = _run(FW + "/sim_main.spl")
expect(code).to_equal(0)

step("Read-back verification after the initial writes")
expect(out).to_contain("read LBA 7 == 8")

step("Overwrites produce stale pages and the newest version reads back")
expect(out).to_contain("LBA 7 reads newest version")

step("Garbage collection reclaims a stale block while the logical view is preserved")
expect(out).to_contain("GC reclaimed at least one block")

step("Trim deallocates an LBA (a later read returns zero)")
expect(out).to_contain("read after trim -> 0")

step("After a power-fail + recovery, committed data survives and trims stay trimmed")
expect(out).to_contain("LBA 50 survives power cycle")
expect(out).to_contain("trimmed LBA 7 stays trimmed after recovery")
expect(out).to_contain("ALL END-TO-END CHECKS PASS")
```

</details>

### NVMe firmware: admin queue + multiple IO queues (controller front end)

#### drives the full admin-and-IO-queue controller lifecycle

- Run the controller end-to-end demo
   - Expected: code equals `0`
- Identify the controller and the namespace via the admin queue
- Create an IO completion queue, then the submission queue bound to it
- Negative: a submission queue bound to a non-existent completion queue is rejected
- A second IO queue pair is created and the controller round-robins both
- Negative: deleting a completion queue with a live bound submission queue is rejected
- Reverse-order teardown deletes the submission queue then the completion queue
- The SMART log reflects the IO, and committed data survives a power cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the controller end-to-end demo")
val (out, err, code) = _run(FW + "/nvme_main.spl")
expect(code).to_equal(0)

step("Identify the controller and the namespace via the admin queue")
expect(out).to_contain("identify controller ok")
expect(out).to_contain("controller reports max IO queues")
expect(out).to_contain("namespace size == LBA_COUNT")

step("Create an IO completion queue, then the submission queue bound to it")
expect(out).to_contain("create IO CQ 1")
expect(out).to_contain("create IO SQ 1 -> CQ 1")

step("Negative: a submission queue bound to a non-existent completion queue is rejected")
expect(out).to_contain("SQ -> missing CQ rejected")

step("A second IO queue pair is created and the controller round-robins both")
expect(out).to_contain("round-robin serviced all 4 across both queues")

step("Negative: deleting a completion queue with a live bound submission queue is rejected")
expect(out).to_contain("delete bound CQ rejected")

step("Reverse-order teardown deletes the submission queue then the completion queue")
expect(out).to_contain("delete SQ 1 ok")
expect(out).to_contain("delete CQ 1 ok")

step("The SMART log reflects the IO, and committed data survives a power cycle")
expect(out).to_contain("SMART shows writes occurred")
expect(out).to_contain("LBA 200 survives power cycle")
expect(out).to_contain("ALL NVME CONTROLLER E2E CHECKS PASS")
```

</details>

### NVMe firmware: production-hardening regressions

#### guards garbage collection against data loss and the write-cliff

- Drive the device to the host-write boundary and run GC under pressure
   - Expected: code equals `0`
- The reserve is held back, GC reclaims safely, and writes resume (no cliff / no loss)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drive the device to the host-write boundary and run GC under pressure")
val (out, err, code) = _run(FW + "/gc_safety_check.spl")
expect(code).to_equal(0)
step("The reserve is held back, GC reclaims safely, and writes resume (no cliff / no loss)")
expect(out).to_contain("GC SAFETY OK")
```

</details>

#### preserves committed data across power loss and a full journal

- Run the power-loss durability check (volatile loss + recovery + WAL overflow)
   - Expected: code equals `0`
- Recovery restores committed writes and 600 writes survive a full WAL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the power-loss durability check (volatile loss + recovery + WAL overflow)")
val (out, err, code) = _run(FW + "/durability_check.spl")
expect(code).to_equal(0)
step("Recovery restores committed writes and 600 writes survive a full WAL")
expect(out).to_contain("DURABILITY OK")
```

</details>

#### relocates data safely during wear-leveling and read-disturb scrub

- Run the static wear-leveling and read-disturb scrub check
   - Expected: code equals `0`
- Both passes reclaim the targeted block with all data preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the static wear-leveling and read-disturb scrub check")
val (out, err, code) = _run(FW + "/wear_scrub_check.spl")
expect(code).to_equal(0)
step("Both passes reclaim the targeted block with all data preserved")
expect(out).to_contain("WEAR/SCRUB OK")
```

</details>

#### preserves the bad-block table and wear history across a Format NVM

- Retire a block + accrue wear, then Format NVM
   - Expected: code equals `0`
- Format erases user data but the retired block and erase counts survive (wear accrues, never resets)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retire a block + accrue wear, then Format NVM")
val (out, err, code) = _run(FW + "/format_check.spl")
expect(code).to_equal(0)
step("Format erases user data but the retired block and erase counts survive (wear accrues, never resets)")
expect(out).to_contain("FORMAT OK")
```

</details>

#### sandboxes dynamic policy hooks so a malicious hook cannot corrupt the FTL (req 7)

- Install custom + evil + over-fuel GC policy hooks and exercise the install gate
   - Expected: code equals `0`
- A custom hook changes GC selection but loses no data; forbidden installs are rejected; over-fuel votes are discarded


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Install custom + evil + over-fuel GC policy hooks and exercise the install gate")
val (out, err, code) = _run(FW + "/policy_hooks_check.spl")
expect(code).to_equal(0)
step("A custom hook changes GC selection but loses no data; forbidden installs are rejected; over-fuel votes are discarded")
expect(out).to_contain("POLICY HOOKS OK")
```

</details>

### NVMe firmware: Lean4 formal verification of the FTL invariants

#### verifies the allocator and GC-reserve safety (Alloc.lean)

- Check proofs/Alloc.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Alloc.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Alloc.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
```

</details>

#### verifies that recovery preserves the committed prefix (Recover.lean)

- Check proofs/Recover.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Recover.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Recover.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
```

</details>

#### verifies the garbage-collection data-loss guard (Gc.lean)

- Check proofs/Gc.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Gc.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Gc.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
```

</details>

#### verifies the sandboxed policy-hook safety properties (Hooks.lean, req 7)

- Check proofs/Hooks.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Hooks.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Hooks.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
```

</details>

#### verifies the flash-controller status state machine (Fmc.lean, gap-closure P1)

- Check proofs/Fmc.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Fmc.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Fmc.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
