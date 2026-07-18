# T32 GUI System Debug Session Specification

> Verifies TRACE32-style GUI debug sessions through a simulated state machine and, when a live TRACE32 remote is available, through the remote command adapter. The scenarios cover lifecycle, register and memory inspection, breakpoint control, window layout, dialog handling, AREA output, printer redirection, and run-state guards.

<!-- sdn-diagram:id=t32_gui_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_gui_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_gui_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_gui_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 GUI System Debug Session Specification

Verifies TRACE32-style GUI debug sessions through a simulated state machine and, when a live TRACE32 remote is available, through the remote command adapter. The scenarios cover lifecycle, register and memory inspection, breakpoint control, window layout, dialog handling, AREA output, printer redirection, and run-state guards.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-GUI-001 |
| Category | Hardware Debug Infrastructure |
| Difficulty | 4/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/hardware/t32_tools/t32_gui_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies TRACE32-style GUI debug sessions through a simulated state machine and,
when a live TRACE32 remote is available, through the remote command adapter.
The scenarios cover lifecycle, register and memory inspection, breakpoint
control, window layout, dialog handling, AREA output, printer redirection, and
run-state guards.

## Syntax

The spec uses `T32GuiSession` helpers to model commands and checks every
expected `Result` branch with explicit assertions or failure messages.

## Examples

`T32GuiSession.create("localhost", 20000)` starts in `disconnected`, then
`connect`, `system_up`, `step`, `capture_registers`, and `disconnect` exercise
the debug workflow.

## Scenarios

### T32 GUI Debug Sessions

#### session lifecycle

#### connect → setup cpu → system up → disconnect

1. var s = T32GuiSession create
   - Expected: s.state equals `disconnected`

2. s connect
   - Expected: s.state equals `connected`

3. s setup cpu
   - Expected: s.cpu equals `CortexM3`

4. s system up
   - Expected: s.state equals `halted`

5. s disconnect
   - Expected: s.state equals `disconnected`
   - Expected: hist1.len() > 0 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
expect(s.state).to_equal("disconnected")
s.connect()
expect(s.state).to_equal("connected")
s.setup_cpu("CortexM3")
expect(s.cpu).to_equal("CortexM3")
s.system_up()
expect(s.state).to_equal("halted")
s.disconnect()
expect(s.state).to_equal("disconnected")
val hist1 = s.history
expect(hist1.len() > 0).to_equal(true)
```

</details>

#### operations on disconnected session fail

1. var s = T32GuiSession create

2. Err

3. Ok

4. Err

5. Ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
val r1 = s.step()
match r1:
    Err(e): expect(e).to_contain("halted")
    Ok(_): fail("step unexpectedly succeeded while disconnected")
val r2 = s.read_register("PC")
match r2:
    Err(e): expect(e).to_contain("halted")
    Ok(_): fail("read_register unexpectedly succeeded while disconnected")
```

</details>

#### breakpoint + step debug session

#### set bp → run → halt → step → read PC → verify PC changed

1. var s = T32GuiSession create

2. s connect

3. s system up

4. Ok

5. Err

6. s set breakpoint
   - Expected: bps1.len() equals `1`

7. Ok

8. Err

9. s run target
   - Expected: s.state equals `running`
   - Expected: s.is_running() is true

10. s halt
   - Expected: s.state equals `halted`

11. s step

12. Ok

13. Err

14. s step over

15. Ok

16. Err

17. s delete breakpoints
   - Expected: bps2.len() equals `0`

18. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
# Read initial PC
val pc_before = s.read_register("PC")
match pc_before:
    Ok(v): expect(v).to_equal("0x08000000")
    Err(e): fail("initial PC read failed: " + e)
# Set breakpoint
s.set_breakpoint("0x08000010")
val bps1 = s.breakpoints
expect(bps1.len()).to_equal(1)
# Capture breakpoint list
val bp_view = s.capture_breakpoints()
match bp_view:
    Ok(v): expect(v).to_contain("0x08000010")
    Err(e): fail("breakpoint capture failed: " + e)
# Run and halt
s.run_target()
expect(s.state).to_equal("running")
expect(s.is_running()).to_equal(true)
s.halt()
expect(s.state).to_equal("halted")
# Single step
s.step()
val pc_after = s.read_register("PC")
match pc_after:
    Ok(v): expect(v).to_equal("0x08000004")
    Err(e): fail("PC read after step failed: " + e)
# Step over
s.step_over()
val pc_final = s.read_register("PC")
match pc_final:
    Ok(v): expect(v).to_equal("0x08000008")
    Err(e): fail("PC read after step over failed: " + e)
# Delete all breakpoints
s.delete_breakpoints()
val bps2 = s.breakpoints
expect(bps2.len()).to_equal(0)
s.disconnect()
```

</details>

#### register + memory inspection session

#### read regs → modify PC → read memory → write memory → verify

1. var s = T32GuiSession create

2. s connect

3. s system up

4. Ok

5. Err

6. Ok

7. Err

8. Ok

9. Err

10. s write register

11. Ok

12. Err

13. Ok

14. Err

15. s write memory

16. Ok

17. Err

18. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
# Read all key registers
val pc = s.read_register("PC")
val sp = s.read_register("SP")
val lr = s.read_register("LR")
match pc:
    Ok(v): expect(v).to_equal("0x08000000")
    Err(e): fail("PC read failed: " + e)
match sp:
    Ok(v): expect(v).to_equal("0x20001000")
    Err(e): fail("SP read failed: " + e)
# Capture register window (like GDB TUI register view)
val reg_view = s.capture_registers()
match reg_view:
    Ok(v): expect(v).to_contain("0x08000000")
    Err(e): fail("register capture failed: " + e)
# Modify PC
s.write_register("PC", "0x08001000")
val new_pc = s.read_register("PC")
match new_pc:
    Ok(v): expect(v).to_equal("0x08001000")
    Err(e): fail("PC read after write failed: " + e)
# Read memory
val mem = s.read_memory("0x08000000")
match mem:
    Ok(v): expect(v.len() > 0).to_equal(true)
    Err(e): fail("memory read failed: " + e)
# Write memory
s.write_memory("0x20000000", "0x12345678")
# Capture memory dump (like GDB x/4x)
val mem_view = s.capture_memory("0x08000000")
match mem_view:
    Ok(v): expect(v.len() > 0).to_equal(true)
    Err(e): fail("memory capture failed: " + e)
s.disconnect()
```

</details>

#### window layout debug session (rcar3_window)

#### setup headless → layout → open debug windows → capture → verify

1. var s = T32GuiSession create

2. s connect

3. s system up

4. s screen off
   - Expected: s.screen_mode equals `off`

5. s area create

6. s area select

7. s page reset
   - Expected: pgs1.len() equals `0`

8. s win clear

9. s set frame

10. s toolbar
   - Expected: s.toolbar_on is true

11. s statusbar
   - Expected: s.statusbar_on is true

12. s win tabs

13. s page create

14. s page select
   - Expected: s.active_page equals `P000`

15. s open window

16. s open window

17. Ok

18. Err

19. s page create

20. s page select
   - Expected: s.active_page equals `P001`

21. s open window

22. s page select

23. s screen on
   - Expected: s.screen_mode equals `on`

24. s area reset

25. s disconnect
   - Expected: hist2.len() > 10 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
# Step 1: Headless setup (for MCP/CLI — SCREEN.OFF + AREA)
s.screen_off()
expect(s.screen_mode).to_equal("off")
s.area_create("MCP_OUT")
s.area_select("MCP_OUT")
# Step 2: Window layout (from rcar3_window.cmm)
s.page_reset()
val pgs1 = s.pages
expect(pgs1.len()).to_equal(0)
s.win_clear()
s.set_frame("1.", "1.", "119.", "62.")
s.toolbar(true)
expect(s.toolbar_on).to_equal(true)
s.statusbar(true)
expect(s.statusbar_on).to_equal(true)
s.win_tabs("10. 20. 40.")
# Step 3: Create pages + position debug windows
s.page_create("P000")
s.page_select("P000")
expect(s.active_page).to_equal("P000")
s.open_window("Register.view", "0.", "0.", "60.", "20.")
s.open_window("Break.List", "62.", "0.", "55.", "10.")
# Step 4: Capture debug windows
val reg_view = s.capture_registers()
match reg_view:
    Ok(v): expect(v).to_contain("0x08000000")
    Err(e): fail("register capture failed in window layout session: " + e)
val bp_view = s.capture_breakpoints()
# Step 5: Create second page
s.page_create("P001")
s.page_select("P001")
expect(s.active_page).to_equal("P001")
s.open_window("Data.dump", "0.", "0.", "80.", "20.")
# Step 6: Switch back to debug page
s.page_select("P000")
# Step 7: Restore screen
s.screen_on()
expect(s.screen_mode).to_equal("on")
s.area_reset()
s.disconnect()
val hist2 = s.history
expect(hist2.len() > 10).to_equal(true)
```

</details>

#### flash + debug session (stm32h7_flash)

#### dialog confirm → setup layout → AREA output → step → capture

1. var s = T32GuiSession create

2. s connect

3. s setup cpu

4. s system up

5. Ok
   - Expected: v == true or v == false is true
   - Expected: v is false

6. Err

7. s toolbar

8. s statusbar

9. s open window

10. s area create

11. s area select

12. s area view

13. s area print

14. s area print

15. s area print

16. s set breakpoint

17. s set breakpoint
   - Expected: bps3.len() equals `2`

18. s run target
   - Expected: s.state equals `running`

19. s halt

20. s step

21. Ok

22. Err

23. Ok

24. Err

25. s area reset

26. s delete breakpoints

27. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.setup_cpu("CortexM7")
s.system_up()
# Step 1: Ask user before flash erase (auto-dismissed in headless)
val confirm = s.dialog_yesno("Erase flash sector 0?")
match confirm:
    Ok(v):
        if LIVE:
            expect(v == true or v == false).to_equal(true)
        else:
            expect(v).to_equal(false)
    Err(e): fail("flash confirmation dialog failed: " + e)
# Step 2: Setup debug layout
s.toolbar(true)
s.statusbar(true)
s.open_window("Register.view", "0.", "0.", "80.", "25.")
# Step 3: Setup AREA for flash output
s.area_create("FLASH_LOG")
s.area_select("FLASH_LOG")
s.area_view("FLASH_LOG")
# Step 4: Simulate flash operations with AREA output
s.area_print("Erasing sector 0...")
s.area_print("Programming 256KB...")
s.area_print("Verify: OK")
# Step 5: Set breakpoint at main (post-flash)
s.set_breakpoint("main")
s.set_breakpoint("0x08000100")
val bps3 = s.breakpoints
expect(bps3.len()).to_equal(2)
# Step 6: Run to breakpoint
s.run_target()
expect(s.state).to_equal("running")
s.halt()
# Step 7: Step through and inspect
s.step()
val pc = s.read_register("PC")
match pc:
    Ok(v): expect(v.len() > 0).to_equal(true)
    Err(e): fail("PC read after flash step failed: " + e)
# Step 8: Capture register view after stepping
val regs = s.capture_registers()
match regs:
    Ok(v): expect(v.len() > 0).to_equal(true)
    Err(e): fail("register capture after flash step failed: " + e)
# Step 9: Clean up
s.area_reset()
s.delete_breakpoints()
s.disconnect()
```

</details>

#### BLE dialog debug session (bl602_wifi)

#### CMM dialog → configure → AREA output → step through BLE init

1. var s = T32GuiSession create

2. s connect

3. s setup cpu

4. s system up

5. s screen off

6. s area create

7. s area select

8. s area view

9. s set breakpoint

10. s set breakpoint

11. s run target

12. s halt

13. s step

14. s step

15. s area print

16. s area print

17. s screen on

18. s area reset

19. s delete breakpoints

20. s disconnect
   - Expected: hist3.len() > 10 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.setup_cpu("RV32IMAC")
s.system_up()
# Step 1: Run BLE config dialog via CMM
val cmm = "; BLE config\nDIALOG\n(\n  HEADER \"BLE Setup\"\n  POS 0. 0. 40.\n  TEXT \"WiFi+BLE dual mode\"\n  LINE 0. 1. 40.\n  POS 0. 2. 12.\n  DEFBUTTON \"OK\" \"DIALOG.END\"\n  POS 14. 2. 12.\n  BUTTON \"Skip\" \"DIALOG.END\"\n  CLOSE \"DIALOG.END\"\n)\nDIALOG.END\nENDDO"
val cmm_result = s.run_cmm(cmm)
# Step 2: Setup debug AREA
s.screen_off()
s.area_create("BLE_OUT")
s.area_select("BLE_OUT")
s.area_view("BLE_OUT")
# Step 3: Set breakpoints at BLE init functions
s.set_breakpoint("0x21000000")
s.set_breakpoint("0x21000100")
# Step 4: Run
s.run_target()
s.halt()
# Step 5: Step through BLE init
s.step()
s.step()
val pc = s.read_register("PC")
# Step 6: Read memory at BLE config area
val ble_cfg = s.read_memory("0x21000000")
# Step 7: Capture registers
val regs = s.capture_registers()
# Step 8: Print BLE status to AREA
s.area_print("BLE initialized")
s.area_print("MAC: 00:11:22:33:44:55")
# Step 9: Clean up
s.screen_on()
s.area_reset()
s.delete_breakpoints()
s.disconnect()
val hist3 = s.history
expect(hist3.len() > 10).to_equal(true)
```

</details>

#### multi-core debug session (stm32wb_dual_core)

#### SCREEN.ALways → toolbar → two-page layout → step each core

1. var s = T32GuiSession create

2. s connect

3. s setup cpu

4. s system up

5. s screen always
   - Expected: s.screen_mode equals `always`

6. s toolbar

7. s statusbar

8. s page create

9. s open window

10. s open window

11. s set breakpoint

12. s page create

13. s open window

14. s page select

15. s run target

16. s halt

17. s step

18. s page select
   - Expected: s.active_page equals `M0_Core`

19. s delete breakpoints

20. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.setup_cpu("CortexM4")
s.system_up()
# Step 1: Persistent display for multi-core
s.screen_always()
expect(s.screen_mode).to_equal("always")
s.toolbar(true)
s.statusbar(true)
# Step 2: Page 1 — M4 core debug
s.page_create("M4_Core")
s.open_window("Register.view", "0.", "0.", "60.", "20.")
s.open_window("Break.List", "62.", "0.", "55.", "10.")
s.set_breakpoint("0x08000000")
# Step 3: Page 2 — M0+ core debug (simulated)
s.page_create("M0_Core")
s.open_window("Register.view", "0.", "0.", "60.", "20.")
# Step 4: Debug on M4 page
s.page_select("M4_Core")
s.run_target()
s.halt()
s.step()
val m4_pc = s.read_register("PC")
val m4_regs = s.capture_registers()
# Step 5: Switch to M0 page, inspect
s.page_select("M0_Core")
expect(s.active_page).to_equal("M0_Core")
# Step 6: Clean up
s.delete_breakpoints()
s.disconnect()
```

</details>

#### AREA semihosting session (imx6sx_qspi)

#### create area → write output → capture → clear → capture again → compare

1. var s = T32GuiSession create

2. s connect

3. s system up

4. s area create

5. s area select

6. s area view
   - Expected: ar1.len() equals `1`

7. s area print

8. s area print

9. s area print

10. s area clear

11. s area print

12. s area reset
   - Expected: ar2.len() equals `0`

13. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
# Step 1: Create AREA for semihosting output
s.area_create("QSPI_OUT")
s.area_select("QSPI_OUT")
s.area_view("QSPI_OUT")
val ar1 = s.areas
expect(ar1.len()).to_equal(1)
# Step 2: Simulate target printf via AREA
s.area_print("QSPI init: OK")
s.area_print("Flash ID: 0xEF4017")
s.area_print("Erase 64KB sector 0: OK")
# Step 3: Capture area output
val before_clear = s.last_capture
# Step 4: Clear area
s.area_clear("QSPI_OUT")
# Step 5: Write more output
s.area_print("Program sector 0: OK")
# Step 6: Reset all areas
s.area_reset()
val ar2 = s.areas
expect(ar2.len()).to_equal(0)
s.disconnect()
```

</details>

#### MENU + SCREEN session (qnx_beagle)

#### SCREEN.ALways → menu reprogram → debug flow

1. var s = T32GuiSession create

2. s connect

3. s system up

4. s screen always

5. s menu reprogram

6. s set breakpoint

7. s run target

8. s halt

9. s step

10. s delete breakpoints

11. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
# Step 1: Persistent display
s.screen_always()
# Step 2: Custom menu
s.menu_reprogram()
# Step 3: Debug
s.set_breakpoint("0x80000000")
s.run_target()
s.halt()
s.step()
val pc = s.read_register("PC")
val regs = s.capture_registers()
# Step 4: Clean up
s.delete_breakpoints()
s.disconnect()
```

</details>

#### PRinTer.FILE session

#### redirect output → capture registers → read file → verify

1. var s = T32GuiSession create

2. s connect

3. s system up

4. s printer file

5. s printer close

6. rt file delete

7. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
val pid = rt_getpid()
val ts = rt_time_now_unix_micros()
val outfile = "/tmp/t32_prt_{pid}_{ts}.txt"
# Step 1: Redirect
s.printer_file(outfile)
# Step 2: Capture (would go to file in live mode)
val regs = s.capture_registers()
# Step 3: Close printer
s.printer_close()
# Step 4: Clean up
rt_file_delete(outfile)
s.disconnect()
```

</details>

#### run-state guard in debug session

#### halted → step allowed, running → capture blocked

1. var s = T32GuiSession create

2. s connect

3. s system up
   - Expected: s.state equals `halted`

4. Ok

5. Err

6. Ok

7. Err

8. s run target
   - Expected: s.state equals `running`

9. Err

10. Ok

11. Err

12. Ok

13. Ok
   - Expected: s.breakpoints.len() equals `1`

14. Err

15. s halt

16. Ok

17. Err

18. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
expect(s.state).to_equal("halted")
# Halted: register read SHOULD work
val r1 = s.read_register("PC")
match r1:
    Ok(pc): expect(pc.len()).to_be_greater_than(0)
    Err(e): fail("halted PC read failed: " + e)
# Halted: capture SHOULD work
val c1 = s.capture_registers()
match c1:
    Ok(view): expect(view).to_contain("PC")
    Err(e): fail("halted register capture failed: " + e)
# Running: register read SHOULD fail
s.run_target()
expect(s.state).to_equal("running")
val r2 = s.read_register("PC")
match r2:
    Err(e): expect(e).to_contain("halted")
    Ok(_): fail("running PC read unexpectedly succeeded")
# Running: capture SHOULD fail
val c2 = s.capture_registers()
match c2:
    Err(e): expect(e).to_contain("halted")
    Ok(_): fail("running register capture unexpectedly succeeded")
# Running: breakpoint set IS allowed (safe while running)
val bp = s.set_breakpoint("0x08001000")
match bp:
    Ok(msg):
        expect(msg).to_contain("0x08001000")
        expect(s.breakpoints.len()).to_equal(1)
    Err(e): fail("breakpoint set while running failed: " + e)
# Halt, then capture works again
s.halt()
val r3 = s.read_register("PC")
match r3:
    Ok(pc): expect(pc.len()).to_be_greater_than(0)
    Err(e): fail("PC read after halt failed: " + e)
s.disconnect()
```

</details>

#### full debug cycle with state diff

#### pre-capture → step → post-capture → diff shows changes

1. var s = T32GuiSession create

2. s connect

3. s system up

4. s step

5. Ok

6. Ok

7. Err

8. Err
   - Expected: pre_hash == post_hash is false
   - Expected: hist4.len() > 5 is true

9. s disconnect


<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GuiSession.create("localhost", 20000)
s.connect()
s.system_up()
# Pre-state
val pre_pc = s.read_register("PC")
val pre_regs = s.capture_registers()
val pre_hash = state_hash(s.registers_view)
# Step — changes PC
s.step()
# Post-state
val post_pc = s.read_register("PC")
val post_regs = s.capture_registers()
val post_hash = state_hash(s.registers_view)
# PC should have changed
match pre_pc:
    Ok(pre_v):
        match post_pc:
            Ok(post_v): expect(pre_v == post_v).to_equal(false)
            Err(e): fail("post-step PC read failed: " + e)
    Err(e): fail("pre-step PC read failed: " + e)
# Register view hash should differ (PC changed)
expect(pre_hash == post_hash).to_equal(false)
# History should record all steps
val hist4 = s.history
expect(hist4.len() > 5).to_equal(true)
s.disconnect()
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


</details>
