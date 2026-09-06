# KV260 SimpleOS rv32 silicon boot qualification

> System test that loads SimpleOS rv32 onto the REAL KV260 (xck26) board through

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# KV260 SimpleOS rv32 silicon boot qualification

System test that loads SimpleOS rv32 onto the REAL KV260 (xck26) board through

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

System test that loads SimpleOS rv32 onto the REAL KV260 (xck26) board through
`scripts/fpga/bringup_kv260_rv32_ddr.shs` (JTAG/xsdb: full psu_init, PL
program, DDR kernel+ramdisk load, core release, JTAG-MMIO transcript readout)
and checks booting. Fail-closed, tiered:

1. **Precondition tier** — Vivado settings, bitstream, kernel ELF, FAT32
   image, and the KV260 FT4232H JTAG interface (USB 0403:6011) must all be
   present. When any is missing the lane records a VISIBLE skip (never a
   silent green) and the live tiers skip with the same reason.
2. **Silicon-liveness tier** — must PASS on a connected board today: PL
   programmed, control-slave CTRL_MAGIC, PRERUN_AXI_READS=0, DDR banner word
   intact after load, core released and executing from DDR (AXI reads grow
   past 1M), UART capture non-empty, hardening canary line printed.
3. **Full-boot tier** — asserts the `.bss` zero-fill held
   (`BSS_HEAPOFF_POST=0x00000000` — un-zeroed .bss on real DDR was the
   boot-loop root cause, fixed in the bringup script) and the full boot
   chain in the JTAG UART capture: `SimpleOS RV32 boot OK`, `FS_MOUNT_OK`,
   `SIMPLEOS_RISCV_SMF_FS_PASS`, `TEST PASSED`, plus the bring-up verdict
   line `PASS: rv32 SimpleOS reached TEST PASSED on KV260 silicon`.
   All three tiers must be GREEN whenever the board is present.

Evidence log: build/fpga/systest/kv260_boot_latest.log (plus a timestamped
copy per run). The board is shared: the runner waits for any live xsdb
session before starting its own bring-up.

## Scenarios

### KV260 SimpleOS rv32 silicon boot (real board, fail-closed)

#### tier 1: detects the KV260 board, JTAG toolchain, and boot artifacts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tier 1: detects the KV260 board, JTAG toolchain, and boot artifacts
- Record the visible skip: KV260 lane not executed on this host
   - Expected: reason == "" is false
- Verify Vivado settings, bitstream, kernel ELF, and FAT32 image exist
- Verify the KV260 FT4232H JTAG interface is on the USB bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 1: detects the KV260 board, JTAG toolchain, and boot artifacts")
"""Board-absent hosts must record a visible skip, never a silent green."""
val reason = _board_absent_reason()
if reason != "":
    skip("kv260 silicon boot preconditions", reason)
    step("Record the visible skip: KV260 lane not executed on this host")
    print "[kv260_boot_spec] SKIP tier1 reason=" + reason
    expect(reason == "").to_equal(false)
else:
    step("Verify Vivado settings, bitstream, kernel ELF, and FAT32 image exist")
    assert_true(rt_file_exists(_vivado_settings()))
    assert_true(rt_file_exists(BITSTREAM))
    assert_true(rt_file_exists(KERNEL_ELF))
    assert_true(rt_file_exists(FAT32_IMG))
    step("Verify the KV260 FT4232H JTAG interface is on the USB bus")
    assert_true(_board_ready())
    print "[kv260_boot_spec] tier1 board-present: xck26 JTAG interface detected"
```

</details>

#### tier 2: programs the PL and proves the soft-core executes SimpleOS from DDR

- tier 2: programs the PL and proves the soft-core executes SimpleOS from DDR
   - Expected: reason == "" is false
- Run the real-board bring-up (JTAG program + psu_init + DDR load + release)
- Verify the PL was programmed and the control slave answered
- Verify the core had not run before release and DDR held the image
- Verify the released core executes from DDR and produced UART output


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 2: programs the PL and proves the soft-core executes SimpleOS from DDR")
"""Silicon-liveness evidence bar the board meets today: psu_init + PL
program + DDR load survive verification and the released core fetches
from DDR (AXI reads grow past 1M) and prints the hardening canary."""
val reason = _board_absent_reason()
if reason != "":
    skip("kv260 silicon liveness", reason)
    print "[kv260_boot_spec] SKIP tier2 reason=" + reason
    expect(reason == "").to_equal(false)
else:
    step("Run the real-board bring-up (JTAG program + psu_init + DDR load + release)")
    val log = _run_bringup()
    step("Verify the PL was programmed and the control slave answered")
    expect(log).to_contain(MARK_PROGRAM_DONE)
    expect(log).to_contain(MARK_CTRL_MAGIC)
    step("Verify the core had not run before release and DDR held the image")
    expect(log).to_contain("SYSTEST_PRERUN_AXI_READS_ZERO=true")
    expect(log).to_contain(MARK_BANNER_WORD)
    step("Verify the released core executes from DDR and produced UART output")
    expect(log).to_contain("SYSTEST_AXI_READS_GT_1M=true")
    expect(log).to_contain("SYSTEST_UART_BYTE_COUNT_POSITIVE=true")
    expect(log).to_contain(MARK_CANARY)
```

</details>

#### tier 3: boots SimpleOS to FS mount and TEST PASSED on silicon

- tier 3: boots SimpleOS to FS mount and TEST PASSED on silicon
   - Expected: reason == "" is false
- Reuse the tier-2 bring-up transcript (single shared-board JTAG run)
- Verify .bss was zero-filled on DDR before core release
- Verify SimpleOS reaches its boot, FS-mount, and pass markers on silicon


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 3: boots SimpleOS to FS mount and TEST PASSED on silicon")
"""Fail-closed full-boot bar: .bss zero-fill held on real DDR and the
kernel reached its final pass markers. NOT skipped on a connected
board."""
val reason = _board_absent_reason()
if reason != "":
    skip("kv260 full boot", reason)
    print "[kv260_boot_spec] SKIP tier3 reason=" + reason
    expect(reason == "").to_equal(false)
else:
    step("Reuse the tier-2 bring-up transcript (single shared-board JTAG run)")
    assert_true(rt_file_exists(LOG_LATEST))
    assert_true(_log_is_fresh())
    val log = _read_log()
    step("Verify .bss was zero-filled on DDR before core release")
    expect(log).to_contain(MARK_BSS_ZEROED)
    step("Verify SimpleOS reaches its boot, FS-mount, and pass markers on silicon")
    expect(log).to_contain(MARK_BOOT_OK)
    expect(log).to_contain(MARK_FS_MOUNT)
    expect(log).to_contain(MARK_SMF_FS_PASS)
    expect(log).to_contain(MARK_TEST_PASSED)
    expect(log).to_contain(MARK_VERDICT_PASS)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `93e4d1f82fad2a26a62f50f5cdd934d7a75fb674fc7b8d12a1139f9009b6a393`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93e4d1f82fad2a26a62f50f5cdd934d7a75fb674fc7b8d12a1139f9009b6a393`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93e4d1f82fad2a26a62f50f5cdd934d7a75fb674fc7b8d12a1139f9009b6a393`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tier 1: detects the KV260 board, JTAG toolchain, and boot artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tier 2: programs the PL and proves the soft-core executes SimpleOS from DDR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tier 3: boots SimpleOS to FS mount and TEST PASSED on silicon' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
