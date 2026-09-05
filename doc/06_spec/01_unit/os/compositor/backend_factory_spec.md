# Boot Screen Backend Selection

> As an operator I want the screen type I asked for whenever the machine can actually drive it, and a logged, explained fallback whenever it cannot — never a blank display. `resolve_screen_type` is the pure decision core: it is handed a runtime profile as a value, so these scenarios can drive the full desktop profile and the capability-free FPGA serial profile through the same function without any device present.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Screen Backend Selection

As an operator I want the screen type I asked for whenever the machine can actually drive it, and a logged, explained fallback whenever it cannot — never a blank display. `resolve_screen_type` is the pure decision core: it is handed a runtime profile as a value, so these scenarios can drive the full desktop profile and the capability-free FPGA serial profile through the same function without any device present.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | simpleos-config-screen-selection |
| Category | OS / Compositor / Screen Selection |
| Status | In Progress |
| Plan | doc/03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md |
| Source | `test/01_unit/os/compositor/backend_factory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As an operator I want the screen type I asked for whenever the machine can
actually drive it, and a logged, explained fallback whenever it cannot — never
a blank display. `resolve_screen_type` is the pure decision core: it is handed
a runtime profile as a value, so these scenarios can drive the full desktop
profile and the capability-free FPGA serial profile through the same function
without any device present.

## Scenarios

### screen type naming

#### round-trips every supported name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips every supported name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips every supported name")
assert_equal(screen_type_name(screen_type_from_text("wm")), "wm")
assert_equal(screen_type_name(screen_type_from_text("2d")), "2d")
assert_equal(screen_type_name(screen_type_from_text("web")), "web")
assert_equal(screen_type_name(screen_type_from_text("gui")), "gui")
```

</details>

#### maps unknown text to the wm floor

- maps unknown text to the wm floor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps unknown text to the wm floor")
assert_equal(screen_type_name(screen_type_from_text("quake")), "wm")
```

</details>

#### maps each type to the capability it needs

- maps each type to the capability it needs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps each type to the capability it needs")
assert_equal(screen_capability_key(screen_type_from_text("wm")), "wm")
assert_equal(screen_capability_key(screen_type_from_text("2d")), "simple2d-engine2d")
assert_equal(screen_capability_key(screen_type_from_text("web")), "framebuffer")
assert_equal(screen_capability_key(screen_type_from_text("gui")), "framebuffer")
```

</details>

### resolve_screen_type on a fully capable desktop profile

#### grants 2d when the engine2d capability is present

- grants 2d when the engine2d capability is present
- Request the 2d screen on the QEMU riscv64 desktop profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("grants 2d when the engine2d capability is present")
step("Request the 2d screen on the QEMU riscv64 desktop profile")
val decided = resolve_screen_type("2d", qemu_riscv64_desktop_profile())
assert_equal(decided.0, "2d")
assert_equal(decided.1, "")
```

</details>

#### grants gui when the surface capability is present

- grants gui when the surface capability is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("grants gui when the surface capability is present")
val decided = resolve_screen_type("gui", qemu_riscv64_desktop_profile())
assert_equal(decided.0, "gui")
assert_equal(decided.1, "")
```

</details>

#### grants web when the surface capability is present

- grants web when the surface capability is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("grants web when the surface capability is present")
val decided = resolve_screen_type("web", qemu_riscv64_desktop_profile())
assert_equal(decided.0, "web")
assert_equal(decided.1, "")
```

</details>

### resolve_screen_type falls closed on a capability-free profile

#### falls back to wm with a reason when 2d is unsupported

- falls back to wm with a reason when 2d is unsupported
- Request the 2d screen on the FPGA serial-only profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to wm with a reason when 2d is unsupported")
step("Request the 2d screen on the FPGA serial-only profile")
val decided = resolve_screen_type("2d", fpga_riscv64_serial_profile())
assert_equal(decided.0, "wm")
assert_equal(decided.1, "unsupported:2d:simple2d-engine2d")
```

</details>

#### falls back to wm with a reason when web is unsupported

- falls back to wm with a reason when web is unsupported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to wm with a reason when web is unsupported")
val decided = resolve_screen_type("web", fpga_riscv64_serial_profile())
assert_equal(decided.0, "wm")
assert_equal(decided.1, "unsupported:web:framebuffer")
```

</details>

#### falls back to wm with a reason when gui is unsupported

- falls back to wm with a reason when gui is unsupported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to wm with a reason when gui is unsupported")
val decided = resolve_screen_type("gui", fpga_riscv64_serial_profile())
assert_equal(decided.0, "wm")
assert_equal(decided.1, "unsupported:gui:framebuffer")
```

</details>

### wm is the never-blank floor

#### resolves wm cleanly on the desktop profile

- resolves wm cleanly on the desktop profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves wm cleanly on the desktop profile")
val decided = resolve_screen_type("wm", qemu_riscv64_desktop_profile())
assert_equal(decided.0, "wm")
assert_equal(decided.1, "")
```

</details>

#### resolves wm cleanly even when the profile declares no wm support

- resolves wm cleanly even when the profile declares no wm support
- The FPGA profile has supports_wm false; wm must still be granted


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves wm cleanly even when the profile declares no wm support")
step("The FPGA profile has supports_wm false; wm must still be granted")
val decided = resolve_screen_type("wm", fpga_riscv64_serial_profile())
assert_equal(decided.0, "wm")
assert_equal(decided.1, "")
```

</details>

#### resolves unknown text to wm with no fallback reason

- resolves unknown text to wm with no fallback reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves unknown text to wm with no fallback reason")
val decided = resolve_screen_type("quake", qemu_riscv64_desktop_profile())
assert_equal(decided.0, "wm")
assert_equal(decided.1, "")
```

</details>

### boot log reason rendering

#### renders a clean selection as none

- renders a clean selection as none


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("renders a clean selection as none")
assert_equal(screen_selection_reason_or_none(""), "none")
```

</details>

#### passes a real reason through unchanged

- passes a real reason through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("passes a real reason through unchanged")
assert_equal(screen_selection_reason_or_none("unsupported:2d:simple2d-engine2d"), "unsupported:2d:simple2d-engine2d")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c5ed3b3d68a80271d12f4e50c9ff283a18d7ecbc8cf9be33ac6a34b4dc3f23e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c5ed3b3d68a80271d12f4e50c9ff283a18d7ecbc8cf9be33ac6a34b4dc3f23e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c5ed3b3d68a80271d12f4e50c9ff283a18d7ecbc8cf9be33ac6a34b4dc3f23e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/backend_factory_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/backend_factory_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/backend_factory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/backend_factory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/backend_factory_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every supported name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/backend_factory_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps unknown text to the wm floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/backend_factory_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps each type to the capability it needs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
