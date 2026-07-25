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
| 30 | 30 | 0 | 0 |

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
| Updated | 2026-07-08 |
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

### NVMe firmware: layered smoke (Firmware / HIL / FTL / FIL)

#### passes the layered firmware smoke

- Run the short layered firmware smoke
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the short layered firmware smoke")
val (out, err, code) = _run(FW + "/fw_layer_smoke.spl")
expect(code).to_equal(0)
expect(out).to_contain("FW LAYER SMOKE PASS")
_expect_no_fail_marker(out, "layered firmware smoke")
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
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
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
_expect_no_fail_marker(out, "end-to-end SSD simulation")
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
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the controller end-to-end demo")
val (out, err, code) = _run(FW + "/nvme_main.spl")
expect(code).to_equal(0)

step("Identify the controller and the namespace via the admin queue")
expect(out).to_contain("identify controller ok")
expect(out).to_contain("controller reports max IO queues")
expect(out).to_contain("namespace size == LBA_COUNT")
expect(out).to_contain("identify invalid namespace rejected")

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
_expect_no_fail_marker(out, "controller end-to-end demo")
```

</details>

### NVMe firmware: production-hardening regressions

#### guards garbage collection against data loss and the write-cliff

- Drive the device to the host-write boundary and run GC under pressure
- The reserve is held back, GC reclaims safely, and writes resume (no cliff / no loss)
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drive the device to the host-write boundary and run GC under pressure")
# ponytail: keep this one noisy nested run out of process_run capture; the full log stays as an artifact.
val (out, err, code) = _shell("mkdir -p build/test-artifacts; SIMPLE_TIMEOUT_SECONDS=60 bin/simple run " + FW + "/gc_safety_check.spl > build/test-artifacts/nvme_gc_safety.out 2> build/test-artifacts/nvme_gc_safety.err && grep -F 'GC SAFETY OK' build/test-artifacts/nvme_gc_safety.out")
step("The reserve is held back, GC reclaims safely, and writes resume (no cliff / no loss)")
expect(code).to_equal(0)
```

</details>

#### preserves committed data across power loss and a full journal

- Run the power-loss durability check (volatile loss + recovery + WAL overflow)
   - Expected: code equals `0`
- Recovery restores committed writes and 600 writes survive a full WAL
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the power-loss durability check (volatile loss + recovery + WAL overflow)")
val (out, err, code) = _run(FW + "/durability_check.spl")
expect(code).to_equal(0)
step("Recovery restores committed writes and 600 writes survive a full WAL")
expect(out).to_contain("DURABILITY OK")
_expect_no_fail_marker(out, "durability check")
```

</details>

#### relocates data safely during wear-leveling and read-disturb scrub

- Run the static wear-leveling and read-disturb scrub check
   - Expected: code equals `0`
- Both passes reclaim the targeted block with all data preserved
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the static wear-leveling and read-disturb scrub check")
val (out, err, code) = _run(FW + "/wear_scrub_check.spl")
expect(code).to_equal(0)
step("Both passes reclaim the targeted block with all data preserved")
expect(out).to_contain("WEAR/SCRUB OK")
_expect_no_fail_marker(out, "wear scrub check")
```

</details>

#### preserves the bad-block table and wear history across a Format NVM

- Retire a block + accrue wear, then Format NVM
   - Expected: code equals `0`
- Format erases user data but the retired block and erase counts survive (wear accrues, never resets)
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retire a block + accrue wear, then Format NVM")
val (out, err, code) = _run(FW + "/format_check.spl")
expect(code).to_equal(0)
step("Format erases user data but the retired block and erase counts survive (wear accrues, never resets)")
expect(out).to_contain("FORMAT OK")
_expect_no_fail_marker(out, "format check")
```

</details>

#### sandboxes dynamic policy hooks so a malicious hook cannot corrupt the FTL (req 7)

- Install custom + evil + over-fuel GC policy hooks and exercise the install gate
   - Expected: code equals `0`
- A custom hook changes GC selection but loses no data; forbidden installs are rejected; over-fuel votes are discarded
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Install custom + evil + over-fuel GC policy hooks and exercise the install gate")
val (out, err, code) = _run(FW + "/policy_hooks_check.spl")
expect(code).to_equal(0)
step("A custom hook changes GC selection but loses no data; forbidden installs are rejected; over-fuel votes are discarded")
expect(out).to_contain("POLICY HOOKS OK")
_expect_no_fail_marker(out, "policy hooks check")
```

</details>

#### corrects one silent payload bit and fails double-bit corruption closed (gap-closure P3)

- Program a NAND page, corrupt one payload bit under stored OOB ECC, and read through FIL
   - Expected: code equals `0`
- The FIL caller receives corrected data for one bit; two silent payload bits report media failure
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Program a NAND page, corrupt one payload bit under stored OOB ECC, and read through FIL")
val (out, err, code) = _run(FW + "/ecc_check.spl")
expect(code).to_equal(0)
step("The FIL caller receives corrected data for one bit; two silent payload bits report media failure")
expect(out).to_contain("ECC OK")
_expect_no_fail_marker(out, "ECC check")
```

</details>

#### moves multi-block host data through segmented PRP descriptors (gap-closure P4)

- Submit a write whose simulated host buffer crosses from PRP segment 1 to PRP segment 2
   - Expected: code equals `0`
- The HIL writes bytes from both PRP segments in LBA order
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a write whose simulated host buffer crosses from PRP segment 1 to PRP segment 2")
val (out, err, code) = _run(FW + "/host_transport_check.spl")
expect(code).to_equal(0)
step("The HIL writes bytes from both PRP segments in LBA order")
expect(out).to_contain("HOST TRANSPORT OK")
_expect_no_fail_marker(out, "host transport check")
```

</details>

#### bounds host writes behind a DRAM arena span with no partial media update (gap-closure P5)

- Fill a DRAM arena span, then submit one write larger than the DRAM budget
   - Expected: code equals `0`
- The oversized write is rejected before any LBA is programmed
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill a DRAM arena span, then submit one write larger than the DRAM budget")
val (out, err, code) = _run(FW + "/dram_buffer_check.spl")
expect(code).to_equal(0)
step("The oversized write is rejected before any LBA is programmed")
expect(out).to_contain("DRAM BUFFER OK")
_expect_no_fail_marker(out, "DRAM buffer check")
```

</details>

#### fails closed when task-pool allocation is unavailable

- Run HIL and controller writes with task-pool allocation disabled
   - Expected: code equals `0`
- Writes return namespace-not-ready and leave media unchanged
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run HIL and controller writes with task-pool allocation disabled")
val (out, err, code) = _run(FW + "/task_pool_fail_closed_check.spl")
expect(code).to_equal(0)
step("Writes return namespace-not-ready and leave media unchanged")
expect(out).to_contain("TASK POOL CLOSED OK")
_expect_no_fail_marker(out, "task pool fail-closed check")
```

</details>

#### schedules NAND ops across channels in parallel with per-channel serialization (gap-closure P2)

- Stripe a write batch across the channels and drain the multi-channel scheduler
   - Expected: code equals `0`
- A striped batch drains in ceil(n/channels) parallel steps; an unbalanced batch is bounded by its deepest channel
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stripe a write batch across the channels and drain the multi-channel scheduler")
val (out, err, code) = _run(FW + "/parallelism_check.spl")
expect(code).to_equal(0)
step("A striped batch drains in ceil(n/channels) parallel steps; an unbalanced batch is bounded by its deepest channel")
expect(out).to_contain("PARALLELISM OK")
_expect_no_fail_marker(out, "parallelism check")
```

</details>

#### reconstructs a failed channel from XOR parity with no data loss (RAIN, gap-closure P8)

- Write a parity stripe across the channels, then fail a channel and reconstruct
   - Expected: code equals `0`
- Any single channel (data or parity) is recovered exactly from the survivors
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a parity stripe across the channels, then fail a channel and reconstruct")
val (out, err, code) = _run(FW + "/rain_check.spl")
expect(code).to_equal(0)
step("Any single channel (data or parity) is recovered exactly from the survivors")
expect(out).to_contain("RAIN OK")
_expect_no_fail_marker(out, "RAIN check")
```

</details>

#### rebuilds a failed channel inside the live FTL with no logical data loss (RAIN wired, P8)

- Write known data through the FTL, fail a whole channel, then rebuild it from live parity
   - Expected: code equals `0`
- Every LBA reads back its original value through the normal FTL read path after the rebuild
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write known data through the FTL, fail a whole channel, then rebuild it from live parity")
val (out, err, code) = _run(FW + "/rain_ftl_check.spl")
expect(code).to_equal(0)
step("Every LBA reads back its original value through the normal FTL read path after the rebuild")
expect(out).to_contain("RAIN-FTL OK")
_expect_no_fail_marker(out, "RAIN FTL check")
```

</details>

#### throttles under sustained thermal load and recovers when cool (gap-closure P7)

- Drive sustained load until the device throttles and raises the SMART critical warning, then cool it
   - Expected: code equals `0`
- The throttle engages over the threshold and releases once the device cools — no crash
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drive sustained load until the device throttles and raises the SMART critical warning, then cool it")
val (out, err, code) = _run(FW + "/thermal_check.spl")
expect(code).to_equal(0)
step("The throttle engages over the threshold and releases once the device cools — no crash")
expect(out).to_contain("THERMAL OK")
_expect_no_fail_marker(out, "thermal check")
```

</details>

#### rejects IO queue deletion while commands or completions are still pending

- Run the focused queue-set delete regression check
   - Expected: code equals `0`
- Rejected deletes preserve pending SQ/CQ work until the host drains it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the focused queue-set delete regression check")
val (out, err, code) = _run(FW + "/qset_delete_check.spl")
expect(code).to_equal(0)
step("Rejected deletes preserve pending SQ/CQ work until the host drains it")
expect(out).to_contain("QSET DELETE OK")
```

</details>

#### backs off instead of dropping work when queue metadata is corrupted

- Run the focused admin/IO queue backpressure regression check
   - Expected: code equals `0`
- Both admin and IO commands remain pending until corrupted queue metadata is repaired


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the focused admin/IO queue backpressure regression check")
val (out, err, code) = _run(FW + "/queue_tail_backpressure_check.spl")
expect(code).to_equal(0)
step("Both admin and IO commands remain pending until corrupted queue metadata is repaired")
expect(out).to_contain("QUEUE BACKPRESSURE OK")
```

</details>

#### preserves legacy HIL work when queue metadata is corrupted

- Run the focused legacy HIL queue backpressure regression check
   - Expected: code equals `0`
- The HIL command remains pending until corrupted queue metadata is repaired


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the focused legacy HIL queue backpressure regression check")
val (out, err, code) = _run(FW + "/hil_queue_backpressure_check.spl")
expect(code).to_equal(0)
step("The HIL command remains pending until corrupted queue metadata is repaired")
expect(out).to_contain("HIL QUEUE BACKPRESSURE OK")
```

</details>

### NVMe firmware: Lean4 formal verification of the FTL invariants

#### verifies the allocator and GC-reserve safety (Alloc.lean)

- Check proofs/Alloc.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Alloc.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Alloc.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Alloc.lean")
```

</details>

#### verifies that recovery preserves the committed prefix (Recover.lean)

- Check proofs/Recover.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Recover.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Recover.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Recover.lean")
```

</details>

#### verifies the garbage-collection data-loss guard (Gc.lean)

- Check proofs/Gc.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Gc.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Gc.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Gc.lean")
```

</details>

#### verifies the sandboxed policy-hook safety properties (Hooks.lean, req 7)

- Check proofs/Hooks.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Hooks.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Hooks.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Hooks.lean")
```

</details>

#### verifies the flash-controller status state machine (Fmc.lean, gap-closure P1)

- Check proofs/Fmc.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Fmc.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Fmc.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Fmc.lean")
```

</details>

#### verifies XOR-parity channel reconstruction (Rain.lean, gap-closure P8)

- Check proofs/Rain.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Rain.lean with the Lean toolchain")
val (out, err, code) = _lean(FW + "/proofs/Rain.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Rain.lean")
```

</details>

### NVMe firmware: production documentation hygiene

#### has no conflict markers in the firmware status docs

- Scan the production-facing firmware docs for unresolved conflict markers
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Scan the production-facing firmware docs for unresolved conflict markers")
val (out, err, code) = _shell("! rg -n '<<<<<<<|=======|>>>>>>>' examples/09_embedded/simpleos_nvme_fw/fw/README.md examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md doc/03_plan/hardware/nvme_fw_gap_closure_plan.md")
expect(code).to_equal(0)
```

</details>

#### keeps rv32 P9 production docs aligned with the hardened scalar floor

- Reject stale wording that narrows the rv32 firmware floor back to RAIN-only
   - Expected: stale_code equals `0`
- Require the production docs to name the rv32 scalar firmware floor and OpenSSD target profile
   - Expected: floor_code equals `0`
- Require the rv32/P9 docs to keep the task-pool fail-closed floor visible
   - Expected: pool_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject stale wording that narrows the rv32 firmware floor back to RAIN-only")
val (stale_out, stale_err, stale_code) = _shell("! rg -n 'Status \\(2026-06-30\\): PLANNED|rv32 RAIN self-test/reference|rv32 RAIN reference|bare-metal \\*\\*rv32\\*\\* RAIN|direct-smoke image (now )?boots|QEMU-booted direct-smoke|Verified 2026-07-07|now builds a small rv32 ELF|builds a fast direct rv32 smoke ELF' examples/09_embedded/simpleos_nvme_fw/fw/README.md examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md doc/03_plan/hardware/nvme_fw_gap_closure_plan.md doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide.md doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide_tldr.md")
expect(stale_code).to_equal(0)

step("Require the production docs to name the rv32 scalar firmware floor and OpenSSD target profile")
val (floor_out, floor_err, floor_code) = _shell("rg -n 'rv32 scalar firmware floor|Cosmos\\+ OpenSSD target profile' examples/09_embedded/simpleos_nvme_fw/fw/README.md examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md doc/03_plan/hardware/nvme_fw_gap_closure_plan.md")
expect(floor_code).to_equal(0)
expect(floor_out).to_contain("rv32 scalar firmware floor")
expect(floor_out).to_contain("Cosmos+ OpenSSD target profile")

step("Require the rv32/P9 docs to keep the task-pool fail-closed floor visible")
val (pool_out, pool_err, pool_code) = _shell("rg -n 'task-pool fail-closed|task-pool-fail-closed' examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md doc/03_plan/hardware/nvme_fw_gap_closure_plan.md examples/09_embedded/simpleos_nvme_fw/fw_rv32/README.md")
expect(pool_code).to_equal(0)
expect(pool_out).to_contain("task-pool")
```

</details>

#### keeps rv64 P9 production docs honest about the missing real-boot ELF

- Require production docs to name the rv64 direct-build recipe and current ELF blocker
   - Expected: rv64_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production docs to name the rv64 direct-build recipe and current ELF blocker")
val (rv64_out, rv64_err, rv64_code) = _shell("rg -n 'fw_rv64/build.shs|rv64 direct-build|build/nvme_fw_rv64\\.elf|nvme_fw_rv64_direct_build_timeout_2026-07-07' examples/09_embedded/simpleos_nvme_fw/fw/README.md examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md doc/03_plan/hardware/nvme_fw_gap_closure_plan.md")
expect(rv64_code).to_equal(0)
expect(rv64_out).to_contain("fw_rv64/build.shs")
expect(rv64_out).to_contain("build/nvme_fw_rv64.elf")
expect(rv64_out).to_contain("nvme_fw_rv64_direct_build_timeout_2026-07-07")
```

</details>

#### keeps firmware self-test assertion counts current in production docs

- Reject stale self-test assertion counts in operator docs
   - Expected: stale_code equals `0`
   - Expected: count_code equals `0`
   - Expected: namespace_doc_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject stale self-test assertion counts in operator docs")
val docs = "examples/09_embedded/simpleos_nvme_fw/fw/README.md doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide.md doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide_tldr.md"
val (stale_out, stale_err, stale_code) = _shell("! rg -n '(526|1167|1170) (checks|asserts|assertions)' " + docs)
expect(stale_code).to_equal(0)
val (count_out, count_err, count_code) = _shell("rg -n '1174 (checks|asserts|assertions)' " + docs)
expect(count_code).to_equal(0)
expect(count_out).to_contain("1174")
val namespace_docs = "doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide.md doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide_tldr.md examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md"
val (namespace_doc_out, namespace_doc_err, namespace_doc_code) = _shell("rg -n 'invalid namespace rejected|invalid namespace rejection|Invalid Identify Namespace|invalid.*namespace' " + namespace_docs)
expect(namespace_doc_code).to_equal(0)
expect(namespace_doc_out).to_contain("invalid namespace")
```

</details>

#### keeps the Cosmos+ OpenSSD platform descriptor executable and honest

- Run the Zynq-7000 / Cosmos+ platform descriptor
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the Zynq-7000 / Cosmos+ platform descriptor")
val (out, err, code) = _run("src/os/kernel/arch/arm32/platform/cosmos_openssd.spl")
expect(code).to_equal(0)
expect(out).to_contain("COSMOS+ OpenSSD platform descriptor OK")
expect(out).to_contain("present firmware seams: 6")
expect(out).to_contain("missing for silicon:    7")
expect(out).to_contain("Zynq NAND Flash Controller")
expect(out).to_contain("PCIe endpoint init")
expect(out).to_contain("DDR controller + OCM init")
expect(out).to_contain("Cortex-A9 SMP + GIC bring-up")
expect(out).to_contain("MMU + L1/L2")
expect(out).to_contain("FSBL / BootROM handoff")
expect(out).to_contain("ARMv7 freestanding Simple runtime")
_expect_no_fail_marker(out, "Cosmos+ OpenSSD platform descriptor")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
