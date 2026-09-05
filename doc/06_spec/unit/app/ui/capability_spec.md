# Capability Specification

> Tests covering Capability, NotSupported.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Specification

## Scenarios

### Capability

#### names each capability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names each capability
   - Expected: capability_name(Capability.Mouse) equals `mouse input`
   - Expected: capability_name(Capability.Color) equals `color output`
   - Expected: capability_name(Capability.Images) equals `image rendering`
   - Expected: capability_name(Capability.Touch) equals `touch input`
   - Expected: capability_name(Capability.NativeDialogs) equals `native dialogs`
   - Expected: capability_name(Capability.Clipboard) equals `clipboard access`
   - Expected: capability_name(Capability.Notification) equals `notifications`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names each capability")
expect(capability_name(Capability.Mouse)).to_equal("mouse input")
expect(capability_name(Capability.Color)).to_equal("color output")
expect(capability_name(Capability.Images)).to_equal("image rendering")
expect(capability_name(Capability.Touch)).to_equal("touch input")
expect(capability_name(Capability.NativeDialogs)).to_equal("native dialogs")
expect(capability_name(Capability.Clipboard)).to_equal("clipboard access")
expect(capability_name(Capability.Notification)).to_equal("notifications")
```

</details>

#### checks capability membership

- checks capability membership
   - Expected: has_capability(caps, Capability.Mouse) is true
   - Expected: has_capability(caps, Capability.Color) is true
   - Expected: has_capability(caps, Capability.Images) is false
   - Expected: has_capability(caps, Capability.Touch) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks capability membership")
val caps = [Capability.Mouse, Capability.Color]
expect(has_capability(caps, Capability.Mouse)).to_equal(true)
expect(has_capability(caps, Capability.Color)).to_equal(true)
expect(has_capability(caps, Capability.Images)).to_equal(false)
expect(has_capability(caps, Capability.Touch)).to_equal(false)
```

</details>

### NotSupported

#### creates with basic constructor

- creates with basic constructor
   - Expected: ns.backend_name equals `tui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with basic constructor")
val ns = NotSupported.new(Capability.Images, "tui")
expect(ns.backend_name).to_equal("tui")
expect(ns.message()).to_contain("tui")
expect(ns.message()).to_contain("image rendering")
```

</details>

#### creates with hint

- creates with hint
   - Expected: ns.fallback_hint equals `not yet wired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with hint")
val ns = NotSupported.with_hint(Capability.Clipboard, "tauri", "not yet wired")
expect(ns.message()).to_contain("not yet wired")
expect(ns.message()).to_contain("clipboard access")
expect(ns.fallback_hint).to_equal("not yet wired")
```

</details>

#### forces callers to handle Result

- forces callers to handle Result
   - Expected: false is true
   - Expected: ns.backend_name equals `tui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forces callers to handle Result")
val result: Result<bool, NotSupported> = Err(NotSupported.new(Capability.Images, "tui"))
match result:
    Ok(_) =>
        expect(false).to_equal(true)  # should not reach
    Err(ns) =>
        expect(ns.backend_name).to_equal("tui")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Capability, NotSupported.
- Capability
- NotSupported

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `ab69b12f0e23675272593bf660f4c4f6c0948527bf4ce39a91cae7ee5362b658`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab69b12f0e23675272593bf660f4c4f6c0948527bf4ce39a91cae7ee5362b658`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab69b12f0e23675272593bf660f4c4f6c0948527bf4ce39a91cae7ee5362b658`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/capability_spec.spl
mirror: doc/06_spec/unit/app/ui/capability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/capability_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names each capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/capability_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks capability membership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/capability_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with basic constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
