# SimpleOS WM pointer step — button and kind code decode

> The SimpleOS window manager receives pointer events as raw PS/2 status bytes from `compositor.spl`'s `_handle_input_ps2` / `_ps2_wm_pointer_button_code` (bits 0/1/2 of the status byte). Before those raw codes reach `handle_pending_wm_pointer_step` in `shell.spl`, two pure decode helpers — defined in the standalone `os.desktop.wm_pointer_decode` module and imported by `shell.spl` — translate them into the text labels the rest of the WM understands: `wm_pointer_button_from_code` (button 0-3 -> none/left/middle/right) and `wm_pointer_kind_from_code` (kind 0-3 -> none/down/up/move). This is a compile-only smoke spec covering the decode contract in isolation — no PS/2 device or compositor bring-up required, and no dependency on the wider desktop/compositor/VFS module graph `shell.spl` pulls in — so a future refactor of the producer side can't silently change what a given code decodes to.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM pointer step — button and kind code decode

The SimpleOS window manager receives pointer events as raw PS/2 status bytes from `compositor.spl`'s `_handle_input_ps2` / `_ps2_wm_pointer_button_code` (bits 0/1/2 of the status byte). Before those raw codes reach `handle_pending_wm_pointer_step` in `shell.spl`, two pure decode helpers — defined in the standalone `os.desktop.wm_pointer_decode` module and imported by `shell.spl` — translate them into the text labels the rest of the WM understands: `wm_pointer_button_from_code` (button 0-3 -> none/left/middle/right) and `wm_pointer_kind_from_code` (kind 0-3 -> none/down/up/move). This is a compile-only smoke spec covering the decode contract in isolation — no PS/2 device or compositor bring-up required, and no dependency on the wider desktop/compositor/VFS module graph `shell.spl` pulls in — so a future refactor of the producer side can't silently change what a given code decodes to.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/wm_pointer_decode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The SimpleOS window manager receives pointer events as raw PS/2 status
bytes from `compositor.spl`'s `_handle_input_ps2` /
`_ps2_wm_pointer_button_code` (bits 0/1/2 of the status byte). Before
those raw codes reach `handle_pending_wm_pointer_step` in `shell.spl`,
two pure decode helpers — defined in the standalone
`os.desktop.wm_pointer_decode` module and imported by `shell.spl` — translate
them into the text labels the rest of the WM understands:
`wm_pointer_button_from_code` (button 0-3 -> none/left/middle/right) and
`wm_pointer_kind_from_code` (kind 0-3 -> none/down/up/move). This is a
compile-only smoke spec covering the decode contract in isolation — no PS/2
device or compositor bring-up required, and no dependency on the wider
desktop/compositor/VFS module graph `shell.spl` pulls in — so a future
refactor of the producer side can't silently change what a given code
decodes to.

## Examples

Each in-range code decodes to its documented label; any out-of-range code
decodes to `"none"` rather than crashing or aliasing another label. Codes
1 for both button and kind (left, down) are pinned as an exact regression
pair, matching the pre-existing value from before this decode logic was
extracted into standalone helpers.

## Scenarios

### SimpleOS WM pointer step — button code decode

#### decodes 0 to none

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes 0 to none
   - Expected: wm_pointer_button_from_code(0) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 0 to none")
expect(wm_pointer_button_from_code(0)).to_equal("none")
```

</details>

#### decodes 1 to left (pre-existing value, must be unchanged)

- decodes 1 to left (pre-existing value, must be unchanged)
   - Expected: wm_pointer_button_from_code(1) equals `left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 1 to left (pre-existing value, must be unchanged)")
expect(wm_pointer_button_from_code(1)).to_equal("left")
```

</details>

#### decodes 2 to middle

- decodes 2 to middle
   - Expected: wm_pointer_button_from_code(2) equals `middle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 2 to middle")
expect(wm_pointer_button_from_code(2)).to_equal("middle")
```

</details>

#### decodes 3 to right

- decodes 3 to right
   - Expected: wm_pointer_button_from_code(3) equals `right`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 3 to right")
expect(wm_pointer_button_from_code(3)).to_equal("right")
```

</details>

#### decodes an unknown button code to none

- decodes an unknown button code to none
   - Expected: wm_pointer_button_from_code(7) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes an unknown button code to none")
expect(wm_pointer_button_from_code(7)).to_equal("none")
```

</details>

### SimpleOS WM pointer step — kind code decode

#### decodes 0 to none

- decodes 0 to none
   - Expected: wm_pointer_kind_from_code(0) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 0 to none")
expect(wm_pointer_kind_from_code(0)).to_equal("none")
```

</details>

#### decodes 1 to down (pre-existing value, must be unchanged)

- decodes 1 to down (pre-existing value, must be unchanged)
   - Expected: wm_pointer_kind_from_code(1) equals `down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 1 to down (pre-existing value, must be unchanged)")
expect(wm_pointer_kind_from_code(1)).to_equal("down")
```

</details>

#### decodes 2 to up

- decodes 2 to up
   - Expected: wm_pointer_kind_from_code(2) equals `up`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 2 to up")
expect(wm_pointer_kind_from_code(2)).to_equal("up")
```

</details>

#### decodes 3 to move

- decodes 3 to move
   - Expected: wm_pointer_kind_from_code(3) equals `move`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 3 to move")
expect(wm_pointer_kind_from_code(3)).to_equal("move")
```

</details>

#### decodes an unknown kind code to none

- decodes an unknown kind code to none
   - Expected: wm_pointer_kind_from_code(9) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes an unknown kind code to none")
expect(wm_pointer_kind_from_code(9)).to_equal("none")
```

</details>

### SimpleOS WM pointer step — left-down regression (exact pre-fix pair)

#### still decodes the original (1, 1) pair to (left, down)

- still decodes the original (1, 1) pair to (left, down)
   - Expected: wm_pointer_button_from_code(1) equals `left`
   - Expected: wm_pointer_kind_from_code(1) equals `down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still decodes the original (1, 1) pair to (left, down)")
expect(wm_pointer_button_from_code(1)).to_equal("left")
expect(wm_pointer_kind_from_code(1)).to_equal("down")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ab0a544fac32f4ab819d91d9d8fd7ae4a239e009470e8e58e3b0c4ea5610c5c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ab0a544fac32f4ab819d91d9d8fd7ae4a239e009470e8e58e3b0c4ea5610c5c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ab0a544fac32f4ab819d91d9d8fd7ae4a239e009470e8e58e3b0c4ea5610c5c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/desktop/wm_pointer_decode_spec.spl
mirror: doc/06_spec/01_unit/os/desktop/wm_pointer_decode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/desktop/wm_pointer_decode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/desktop/wm_pointer_decode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/desktop/wm_pointer_decode_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes 0 to none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_pointer_decode_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes 1 to left (pre-existing value, must be unchanged)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_pointer_decode_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes 2 to middle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
