# T32 CMM GUI Pattern Detection

> Tests that TRACE32 CMM GUI patterns are correctly detected in local CMM fixture files. Reads each .cmm file at runtime, scans every line, and verifies the expected GUI dialog and widget patterns are found.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 CMM GUI Pattern Detection

Tests that TRACE32 CMM GUI patterns are correctly detected in local CMM fixture files. Reads each .cmm file at runtime, scans every line, and verifies the expected GUI dialog and widget patterns are found.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that TRACE32 CMM GUI patterns are correctly detected in local CMM fixture
files. Reads each .cmm file at runtime, scans every line, and verifies the
expected GUI dialog and widget patterns are found.

## Scenarios

### T32 CMM GUI Patterns — live fixture scan

#### rcar3_window.cmm (WinPOS/WinPAGE/FramePOS/TOOLBAR)

#### finds all window layout patterns

- finds all window layout patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds all window layout patterns")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/rcar3_window.cmm")
expect_pattern(patterns,"winpage_reset")
expect_pattern(patterns,"winclear")
expect_pattern(patterns,"framepos")
expect_pattern(patterns,"winpos")
expect_pattern(patterns,"wintabs")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"statusbar")
expect_pattern(patterns,"winpage_create")
expect_pattern(patterns,"winpage_select")
```

</details>

#### spreadtrum_main.cmm (DIALOG block + controls)

#### finds dialog block with all controls

- finds dialog block with all controls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds dialog block with all controls")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/spreadtrum_main.cmm")
expect_pattern(patterns,"dialog_ok")
expect_pattern(patterns,"dialog_block")
expect_pattern(patterns,"header")
expect_pattern(patterns,"pos")
expect_pattern(patterns,"text_label")
expect_pattern(patterns,"defbutton")
expect_pattern(patterns,"button")
expect_pattern(patterns,"close_handler")
expect_pattern(patterns,"dialog_end")
```

</details>

#### bl602_wifi.cmm (DIALOG + LINE separator)

#### finds dialog with line separator

- finds dialog with line separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds dialog with line separator")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/bl602_wifi.cmm")
expect_pattern(patterns,"dialog_block")
expect_pattern(patterns,"header")
expect_pattern(patterns,"defbutton")
expect_pattern(patterns,"button")
expect_pattern(patterns,"line_separator")
expect_pattern(patterns,"close_handler")
```

</details>

#### imx6sx_qspi.cmm (AREA commands)

#### finds all AREA operations

- finds all AREA operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds all AREA operations")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/imx6sx_qspi.cmm")
expect_pattern(patterns,"area_create")
expect_pattern(patterns,"area_select")
expect_pattern(patterns,"area_view")
expect_pattern(patterns,"area_clear")
```

</details>

#### ch32v307_kernel.cmm (AREA + MENU.ReProgram + AREA.RESet)

#### finds AREA with dimensions and AREA.RESet

- finds AREA with dimensions and AREA.RESet


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds AREA with dimensions and AREA.RESet")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/ch32v307_kernel.cmm")
expect_pattern(patterns,"area_create")
expect_pattern(patterns,"area_view")
expect_pattern(patterns,"area_select")
expect_pattern(patterns,"area_reset")
expect_pattern(patterns,"menu_reprogram")
```

</details>

#### sifive_e31_debug.cmm (SCREEN.ALways + WinPOS)

#### finds SCREEN.ALways and window positions

- finds SCREEN.ALways and window positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds SCREEN.ALways and window positions")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/sifive_e31_debug.cmm")
expect_pattern(patterns,"screen_always")
expect_pattern(patterns,"winpos")
```

</details>

#### qnx_beagle.cmm (SCREEN.ALways + MENU.ReProgram)

#### finds SCREEN and MENU patterns

- finds SCREEN and MENU patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds SCREEN and MENU patterns")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/qnx_beagle.cmm")
expect_pattern(patterns,"screen_always")
expect_pattern(patterns,"menu_reprogram")
```

</details>

#### linux_vm.cmm (MENU.ReProgram)

#### finds MENU pattern

- finds MENU pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds MENU pattern")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/linux_vm.cmm")
expect_pattern(patterns,"menu_reprogram")
```

</details>

#### stm32h7_flash.cmm (DIALOG.YESNO + TOOLBAR + WinPOS)

#### finds DIALOG.YESNO and layout

- finds DIALOG.YESNO and layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds DIALOG.YESNO and layout")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/stm32/stm32h7_flash.cmm")
expect_pattern(patterns,"dialog_yesno")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"winpos")
```

</details>

#### stm32wb_ble.cmm (DIALOG.YESNO + TOOLBAR + WinPOS)

#### finds BLE dialog and window layout

- finds BLE dialog and window layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds BLE dialog and window layout")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/stm32/stm32wb_ble.cmm")
expect_pattern(patterns,"dialog_yesno")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"winpos")
```

</details>

#### stm32wb_dual_core.cmm (SCREEN.ALways + TOOLBAR + STATUSBAR + multi-WinPOS)

#### finds multi-core debug layout

- finds multi-core debug layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds multi-core debug layout")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/stm32/stm32wb_dual_core.cmm")
expect_pattern(patterns,"screen_always")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"statusbar")
expect_pattern(patterns,"winpos")
```

</details>

#### stm32h7_swd_debug.cmm (TOOLBAR + STATUSBAR + WinPOS)

#### finds SWD debug layout

- finds SWD debug layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds SWD debug layout")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/stm32/stm32h7_swd_debug.cmm")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"statusbar")
expect_pattern(patterns,"winpos")
```

</details>

#### stm32h7_peripheral.cmm (TOOLBAR + STATUSBAR + WinPOS)

#### finds peripheral viewer layout

- finds peripheral viewer layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds peripheral viewer layout")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/stm32/stm32h7_peripheral.cmm")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"statusbar")
expect_pattern(patterns,"winpos")
```

</details>

#### stm32wb_flash_otp.cmm (double DIALOG.YESNO + TOOLBAR + WinPOS)

#### finds OTP flash patterns

- finds OTP flash patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds OTP flash patterns")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/stm32/stm32wb_flash_otp.cmm")
expect_pattern(patterns,"dialog_yesno")
expect_pattern(patterns,"toolbar")
expect_pattern(patterns,"winpos")
```

</details>

#### esp32c3_flash.cmm (DIALOG.YESNO)

#### finds flash erase dialog

- finds flash erase dialog


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds flash erase dialog")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/esp32c3_flash.cmm")
expect_pattern(patterns,"dialog_yesno")
```

</details>

#### s32k_flash.cmm (DIALOG.YESNO)

#### finds device secure dialog

- finds device secure dialog


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds device secure dialog")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/s32k_flash.cmm")
expect_pattern(patterns,"dialog_yesno")
```

</details>

#### polarfire_program.cmm (DIALOG.OK)

#### finds design file dialog

- finds design file dialog


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds design file dialog")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/polarfire_program.cmm")
expect_pattern(patterns,"dialog_ok")
```

</details>

#### expected_cli conversions have SCREEN.OFF + AREA setup

#### expected_cli/web/rcar3_window.cmm has SCREEN.OFF

- expected_cli/web/rcar3_window.cmm has SCREEN.OFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expected_cli/web/rcar3_window.cmm has SCREEN.OFF")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/web/rcar3_window.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
expect_pattern(patterns,"area_select")
```

</details>

#### expected_cli/web/spreadtrum_main.cmm has SCREEN.OFF

- expected_cli/web/spreadtrum_main.cmm has SCREEN.OFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expected_cli/web/spreadtrum_main.cmm has SCREEN.OFF")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/web/spreadtrum_main.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
```

</details>

#### expected_cli/riscv/bl602_wifi.cmm has SCREEN.OFF

- expected_cli/riscv/bl602_wifi.cmm has SCREEN.OFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expected_cli/riscv/bl602_wifi.cmm has SCREEN.OFF")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/riscv/bl602_wifi.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
```

</details>

#### expected_cli/stm32/stm32wb_dual_core.cmm has SCREEN.OFF

- expected_cli/stm32/stm32wb_dual_core.cmm has SCREEN.OFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expected_cli/stm32/stm32wb_dual_core.cmm has SCREEN.OFF")
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/stm32/stm32wb_dual_core.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
```

</details>

#### non-GUI fixtures have no GUI patterns

#### fe310_blinky.cmm has no GUI

- fe310_blinky.cmm has no GUI
   - Expected: patterns.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fe310_blinky.cmm has no GUI")
if not _has_fixtures:
    expect(_has_fixtures).to_be(false)
else:
    val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/fe310_blinky.cmm")
    expect(patterns.len()).to_equal(0)
```

</details>

#### classifier coverage — all known types

#### classifies SCREEN.ALways

- classifies SCREEN.ALways
   - Expected: cmm_classify_pattern("SCREEN.ALways") equals `screen_always`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies SCREEN.ALways")
expect(cmm_classify_pattern("SCREEN.ALways")).to_equal("screen_always")
```

</details>

#### classifies AREA.RESet

- classifies AREA.RESet
   - Expected: cmm_classify_pattern("AREA.RESet") equals `area_reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies AREA.RESet")
expect(cmm_classify_pattern("AREA.RESet")).to_equal("area_reset")
```

</details>

#### classifies MENU.ReProgram

- classifies MENU.ReProgram
   - Expected: cmm_classify_pattern("MENU.ReProgram ~~/demo/arm/kernel/qnx/qnx.men") equals `menu_reprogram`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies MENU.ReProgram")
expect(cmm_classify_pattern("MENU.ReProgram ~~/demo/arm/kernel/qnx/qnx.men")).to_equal("menu_reprogram")
```

</details>

#### classifies DIALOG.STRing

- classifies DIALOG.STRing
   - Expected: cmm_classify_pattern("DIALOG.STRing(project.name)") equals `dialog_string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies DIALOG.STRing")
expect(cmm_classify_pattern("DIALOG.STRing(project.name)")).to_equal("dialog_string")
```

</details>

#### does not classify non-GUI as GUI

- does not classify non-GUI as GUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not classify non-GUI as GUI")
expect(cmm_is_gui_pattern("SYStem.Up")).to_be(false)
expect(cmm_is_gui_pattern("Break.Set main")).to_be(false)
expect(cmm_is_gui_pattern("Data.dump D:0x0")).to_be(false)
expect(cmm_is_gui_pattern("; comment line")).to_be(false)
expect(cmm_is_gui_pattern("")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `35cbe43bd240916552576315c026c63ffe1d71c6c5a8c2711d9db380b745d2d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35cbe43bd240916552576315c026c63ffe1d71c6c5a8c2711d9db380b745d2d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35cbe43bd240916552576315c026c63ffe1d71c6c5a8c2711d9db380b745d2d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl
mirror: doc/06_spec/03_system/feature/app/t32_tools/t32_cmm_gui_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/t32_tools/t32_cmm_gui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/t32_tools/t32_cmm_gui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds all window layout patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds dialog block with all controls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_cmm_gui_spec.spl:229:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds dialog with line separator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
