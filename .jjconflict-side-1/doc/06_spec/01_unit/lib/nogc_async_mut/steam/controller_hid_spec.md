# Controller Hid Specification

> Tests covering Steam controller HID.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Controller Hid Specification

## Scenarios

### Steam controller HID

#### open with valid path returns is_ok=true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- open with valid path returns is_ok=true
   - Expected: result.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("open with valid path returns is_ok=true")
val result = controller_hid_open("/dev/input/event0")
expect(result.is_ok).to_equal(true)
expect(result.device_id).to_be_greater_than(0)
```

</details>

#### open with empty path returns error

- open with empty path returns error
   - Expected: result.is_ok is false
   - Expected: result.error equals `missing-input-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("open with empty path returns error")
val result = controller_hid_open("")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-input-path")
```

</details>

#### poll returns connected=true for open device

- poll returns connected=true for open device
   - Expected: state.connected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("poll returns connected=true for open device")
val result = controller_hid_open("/dev/input/event0")
val state = controller_hid_poll(result.device_id)
expect(state.connected).to_equal(true)
```

</details>

#### poll returns connected=false for invalid device

- poll returns connected=false for invalid device
   - Expected: state.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("poll returns connected=false for invalid device")
val state = controller_hid_poll(0)
expect(state.connected).to_equal(false)
```

</details>

#### set_buttons updates button state readable via poll

- set_buttons updates button state readable via poll
   - Expected: state.buttons equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set_buttons updates button state readable via poll")
val result = controller_hid_open("/dev/input/event0")
controller_hid_set_buttons(result.device_id, 16)
val state = controller_hid_poll(result.device_id)
expect(state.buttons).to_equal(16)
```

</details>

#### initial button state is zero

- initial button state is zero
   - Expected: state.buttons equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("initial button state is zero")
val result = controller_hid_open("/dev/input/event1")
val state = controller_hid_poll(result.device_id)
expect(state.buttons).to_equal(0)
```

</details>

#### two opens return distinct device IDs

- two opens return distinct device IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two opens return distinct device IDs")
val r1 = controller_hid_open("/dev/input/event0")
val r2 = controller_hid_open("/dev/input/event1")
expect(r1.device_id).to_not_equal(r2.device_id)
```

</details>

#### close makes device unreachable

- close makes device unreachable
   - Expected: state.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("close makes device unreachable")
val result = controller_hid_open("/dev/input/event0")
controller_hid_close(result.device_id)
val state = controller_hid_poll(result.device_id)
expect(state.connected).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Steam controller HID.
- Steam controller HID

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c737c4bf0a25a3ecb1d6a13b3005525199a8112cf821d4d4fbc5b44d94592b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c737c4bf0a25a3ecb1d6a13b3005525199a8112cf821d4d4fbc5b44d94592b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c737c4bf0a25a3ecb1d6a13b3005525199a8112cf821d4d4fbc5b44d94592b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open with valid path returns is_ok=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open with empty path returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'poll returns connected=true for open device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
