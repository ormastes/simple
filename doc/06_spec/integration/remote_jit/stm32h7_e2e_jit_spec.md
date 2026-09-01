# STM32H7 Remote JIT E2E Test

> End-to-end test of the remote JIT pipeline on real STM32H7 hardware. Compiles ARM Thumb-2 code on the host, uploads to SRAM via OpenOCD telnet, executes on the Cortex-M7, and verifies the result register.

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
| Source | `test/integration/remote_jit/stm32h7_e2e_jit_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects hardware availability
   - Expected: openocd_available() is true
   - Expected: cross_tools_available() is true
   - Expected: stlink_probe_detected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects hardware availability")
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

- connects to STM32H7 via OpenOCD and reads SRAM


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects to STM32H7 via OpenOCD and reads SRAM")
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

- compiles ARM Thumb-2 binary on host
   - Expected: size equals `4`
   - Expected: hex_out.stdout.trim() equals `2a2000be`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles ARM Thumb-2 binary on host")
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

- executes ARM code on STM32H7 and returns 42 in R0


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes ARM code on STM32H7 and returns 42 in R0")
"""
Full E2E pipeline:
1. Compile ARM Thumb-2 on host (movs r0, #42; bkpt)
2. Start OpenOCD, connect to STM32H7
3. Reset and halt CPU
4. Write compiled bytes to SRAM at 0x24010000
5. Read back and verify memory contents
6. Clear R0, set PC and SP
7. Resume execution
8. Wait for BKPT halt
9. Read R0 -- should be 42
"""
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31c1106960d2cea5970460a932e8717016f444843886de4a1d6e10b92dd3f796`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31c1106960d2cea5970460a932e8717016f444843886de4a1d6e10b92dd3f796`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31c1106960d2cea5970460a932e8717016f444843886de4a1d6e10b92dd3f796`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/remote_jit/stm32h7_e2e_jit_spec.spl
mirror: doc/06_spec/integration/remote_jit/stm32h7_e2e_jit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/remote_jit/stm32h7_e2e_jit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/remote_jit/stm32h7_e2e_jit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/remote_jit/stm32h7_e2e_jit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/remote_jit/stm32h7_e2e_jit_spec.spl:294:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects hardware availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/stm32h7_e2e_jit_spec.spl:304:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects to STM32H7 via OpenOCD and reads SRAM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/stm32h7_e2e_jit_spec.spl:325:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles ARM Thumb-2 binary on host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
