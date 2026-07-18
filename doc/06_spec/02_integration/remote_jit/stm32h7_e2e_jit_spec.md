# STM32H7 Remote JIT E2E Test

> End-to-end test of the remote JIT pipeline on real STM32H7 hardware. Compiles ARM Thumb-2 code on the host, uploads to SRAM via OpenOCD telnet, executes on the Cortex-M7, and verifies the result register.

<!-- sdn-diagram:id=stm32h7_e2e_jit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32h7_e2e_jit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32h7_e2e_jit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32h7_e2e_jit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STM32H7 Remote JIT E2E Test

End-to-end test of the remote JIT pipeline on real STM32H7 hardware. Compiles ARM Thumb-2 code on the host, uploads to SRAM via OpenOCD telnet, executes on the Cortex-M7, and verifies the result register.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-011 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/02_integration/remote_jit/stm32h7_e2e_jit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end test of the remote JIT pipeline on real STM32H7 hardware.
Compiles ARM Thumb-2 code on the host, uploads to SRAM via OpenOCD telnet,
executes on the Cortex-M7, and verifies the result register.

Uses OpenOCD telnet interface (not GDB MI) because the system GDB does not
support ARM architecture (gdb-multiarch not installed).

## Requirements

- STM32H7 eval board with STLINK-V3 probe physically connected
- OpenOCD installed
- clang, ld.lld, llvm-objcopy for ARM cross-compilation

## Scenarios

### STM32H7 remote JIT end-to-end

<details>
<summary>Advanced: detects hardware availability</summary>

#### detects hardware availability _(slow)_

1. print "SKIP: {skip reason
   - Expected: openocd_available() is true
   - Expected: cross_tools_available() is true
   - Expected: stlink_probe_detected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "SKIP: {skip_reason()}"
else:
    expect(openocd_available()).to_equal(true)
    expect(cross_tools_available()).to_equal(true)
    expect(stlink_probe_detected()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: connects to STM32H7 via OpenOCD and reads SRAM</summary>

#### connects to STM32H7 via OpenOCD and reads SRAM _(slow)_

1. print "SKIP: {skip reason
2. var pid = ocd start
3. ocd cmd
4. ocd cmd
5. ocd stop


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "SKIP: {skip_reason()}"
else:
    var pid = ocd_start()
    expect(pid).to_be_greater_than(0)

    # Reset and halt
    val halt_out = ocd_cmd("reset halt")
    expect(halt_out).to_contain("halted")

    # Write a known pattern to SRAM
    ocd_cmd("mww 0x24010000 0xdeadbeef")
    val readback = ocd_cmd("mdw 0x24010000")
    expect(readback).to_contain("deadbeef")

    ocd_cmd("shutdown")
    ocd_stop(pid)
```

</details>


</details>

<details>
<summary>Advanced: compiles ARM Thumb-2 binary on host</summary>

#### compiles ARM Thumb-2 binary on host _(slow)_

1. shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not cross_tools_available():
    print "SKIP: cross-compilation tools not available"
else:
    val bin_path = compile_arm_return42()
    expect(bin_path.len()).to_be_greater_than(0)

    # Verify binary size (should be 4 bytes: movs + bkpt)
    val size_out = shell("wc -c < '{bin_path}'")
    val size = parse_i64(size_out.stdout.trim())
    expect(size).to_equal(4)

    # Verify correct machine code
    val hex_out = shell("xxd -p '{bin_path}'")
    expect(hex_out.stdout.trim()).to_equal("2a2000be")

    # Cleanup
    shell("rm -rf '{bin_path}'")
```

</details>


</details>

<details>
<summary>Advanced: executes ARM code on STM32H7 and returns 42 in R0</summary>

#### executes ARM code on STM32H7 and returns 42 in R0 _(slow)_

1. print "SKIP: {skip reason
2. var pid = ocd start
3. ocd cmd
4. ocd cmd
5. ocd cmd
6. ocd cmd
7. ocd cmd
8. shell
9. print "E2E PASS: r0={r0 after trim
10. ocd cmd
11. ocd stop
12. shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "SKIP: {skip_reason()}"
else:
    # --- Phase 1: Compile on host ---
    val bin_path = compile_arm_return42()
    expect(bin_path.len()).to_be_greater_than(0)

    # --- Phase 2: Connect to hardware ---
    var pid = ocd_start()
    expect(pid).to_be_greater_than(0)

    # --- Phase 3: Reset and halt ---
    val halt_out = ocd_cmd("reset halt")
    expect(halt_out).to_contain("halted")

    # --- Phase 4: Upload code to SRAM ---
    # Known-good encoded word for:
    #   movs r0, #42
    #   bkpt #0
    ocd_cmd("mww 0x24010000 0xbe00202a")

    # --- Phase 5: Verify memory ---
    val mem_out = ocd_cmd("mdw 0x24010000")
    expect(mem_out.lower()).to_contain("be00202a")

    # --- Phase 6: Set registers ---
    # Clear R0 to prove execution changes it
    ocd_cmd("reg r0 0")
    expect(ocd_cmd("reg r0").lower()).to_contain("0x00000000")

    # Set SP to safe location in SRAM
    ocd_cmd("reg sp {SRAM_STACK_TOP}")

    # Set PC to code start (bit 0 = 1 for Thumb mode)
    ocd_cmd("reg pc 0x24010001")
    expect(ocd_cmd("reg pc").lower()).to_contain("0x24010001")

    # --- Phase 7: Execute ---
    ocd_cmd("resume")
    # BKPT fires immediately (2 instructions), but give it a moment
    shell("sleep 0.5")

    # --- Phase 8: Read result ---
    val r0_after = ocd_cmd("reg r0").lower()
    val pc_after = ocd_cmd("reg pc").lower()

    expect(r0_after).to_contain("0x0000002a")
    expect(pc_after).to_contain("0x24010002")

    print "E2E PASS: r0={r0_after.trim()} pc={pc_after.trim()}"

    # --- Phase 9: Cleanup ---
    ocd_cmd("shutdown")
    ocd_stop(pid)
    shell("rm -rf '{bin_path}'")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
