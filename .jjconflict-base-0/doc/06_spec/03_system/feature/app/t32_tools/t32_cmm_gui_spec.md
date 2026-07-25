# T32 CMM GUI Pattern Detection

> Tests that TRACE32 CMM GUI patterns are correctly detected in local CMM fixture files. Reads each .cmm file at runtime, scans every line, and verifies the expected GUI dialog and widget patterns are found.

<!-- sdn-diagram:id=t32_cmm_gui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cmm_gui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cmm_gui_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cmm_gui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that TRACE32 CMM GUI patterns are correctly detected in local CMM fixture
files. Reads each .cmm file at runtime, scans every line, and verifies the
expected GUI dialog and widget patterns are found.

## Scenarios

### T32 CMM GUI Patterns — live fixture scan

#### rcar3_window.cmm (WinPOS/WinPAGE/FramePOS/TOOLBAR)

#### finds all window layout patterns

1. expect pattern
2. expect pattern
3. expect pattern
4. expect pattern
5. expect pattern
6. expect pattern
7. expect pattern
8. expect pattern
9. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern
4. expect pattern
5. expect pattern
6. expect pattern
7. expect pattern
8. expect pattern
9. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern
4. expect pattern
5. expect pattern
6. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern
4. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern
4. expect pattern
5. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/sifive_e31_debug.cmm")
expect_pattern(patterns,"screen_always")
expect_pattern(patterns,"winpos")
```

</details>

#### qnx_beagle.cmm (SCREEN.ALways + MENU.ReProgram)

#### finds SCREEN and MENU patterns

1. expect pattern
2. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/qnx_beagle.cmm")
expect_pattern(patterns,"screen_always")
expect_pattern(patterns,"menu_reprogram")
```

</details>

#### linux_vm.cmm (MENU.ReProgram)

#### finds MENU pattern

1. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/linux_vm.cmm")
expect_pattern(patterns,"menu_reprogram")
```

</details>

#### stm32h7_flash.cmm (DIALOG.YESNO + TOOLBAR + WinPOS)

#### finds DIALOG.YESNO and layout

1. expect pattern
2. expect pattern
3. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern
4. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern
2. expect pattern
3. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/esp32c3_flash.cmm")
expect_pattern(patterns,"dialog_yesno")
```

</details>

#### s32k_flash.cmm (DIALOG.YESNO)

#### finds device secure dialog

1. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/s32k_flash.cmm")
expect_pattern(patterns,"dialog_yesno")
```

</details>

#### polarfire_program.cmm (DIALOG.OK)

#### finds design file dialog

1. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/web/polarfire_program.cmm")
expect_pattern(patterns,"dialog_ok")
```

</details>

#### expected_cli conversions have SCREEN.OFF + AREA setup

#### expected_cli/web/rcar3_window.cmm has SCREEN.OFF

1. expect pattern
2. expect pattern
3. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/web/rcar3_window.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
expect_pattern(patterns,"area_select")
```

</details>

#### expected_cli/web/spreadtrum_main.cmm has SCREEN.OFF

1. expect pattern
2. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/web/spreadtrum_main.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
```

</details>

#### expected_cli/riscv/bl602_wifi.cmm has SCREEN.OFF

1. expect pattern
2. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/riscv/bl602_wifi.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
```

</details>

#### expected_cli/stm32/stm32wb_dual_core.cmm has SCREEN.OFF

1. expect pattern
2. expect pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    skip:
val patterns = scan_cmm_gui(FIXTURE_BASE + "/expected_cli/stm32/stm32wb_dual_core.cmm")
expect_pattern(patterns,"screen_off")
expect_pattern(patterns,"area_create")
```

</details>

#### non-GUI fixtures have no GUI patterns

#### fe310_blinky.cmm has no GUI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_fixtures:
    expect(_has_fixtures).to_be(false)
else:
    val patterns = scan_cmm_gui(FIXTURE_BASE + "/riscv/fe310_blinky.cmm")
    expect(patterns.len()).to_equal(0)
```

</details>

#### classifier coverage — all known types

#### classifies SCREEN.ALways

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmm_classify_pattern("SCREEN.ALways")).to_equal("screen_always")
```

</details>

#### classifies AREA.RESet

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmm_classify_pattern("AREA.RESet")).to_equal("area_reset")
```

</details>

#### classifies MENU.ReProgram

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmm_classify_pattern("MENU.ReProgram ~~/demo/arm/kernel/qnx/qnx.men")).to_equal("menu_reprogram")
```

</details>

#### classifies DIALOG.STRing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmm_classify_pattern("DIALOG.STRing(project.name)")).to_equal("dialog_string")
```

</details>

#### does not classify non-GUI as GUI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
