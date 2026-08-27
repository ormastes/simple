# Tauri Backend Specification

> Tests covering TauriBackend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Backend Specification

## Scenarios

### TauriBackend

#### creates successfully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates successfully
   - Expected: backend.backend_name() equals `tauri`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates successfully")
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        expect(backend.backend_name()).to_equal("tauri")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### reports correct capabilities

- reports correct capabilities
   - Expected: has_capability(caps, Capability.Mouse) is true
   - Expected: has_capability(caps, Capability.Color) is true
   - Expected: has_capability(caps, Capability.Images) is true
   - Expected: has_capability(caps, Capability.NativeDialogs) is true
   - Expected: has_capability(caps, Capability.Notification) is true
   - Expected: has_capability(caps, Capability.Touch) is false
   - Expected: backend.supports_touch() is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct capabilities")
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Mouse)).to_equal(true)
        expect(has_capability(caps, Capability.Color)).to_equal(true)
        expect(has_capability(caps, Capability.Images)).to_equal(true)
        expect(has_capability(caps, Capability.NativeDialogs)).to_equal(true)
        expect(has_capability(caps, Capability.Notification)).to_equal(true)
        expect(has_capability(caps, Capability.Touch)).to_equal(false)
        expect(backend.supports_touch()).to_equal(false)
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### models Android Tauri WebView as touch capable

- models Android Tauri WebView as touch capable
   - Expected: has_capability(caps, Capability.Touch) is true
   - Expected: backend.supports_touch() is true
   - Expected: backend.supports_mouse() is true
   - Expected: backend.backend_name() equals `tauri`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models Android Tauri WebView as touch capable")
val result = TauriBackend.new_android(3000)
match result:
    Ok(backend) =>
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Touch)).to_equal(true)
        expect(backend.supports_touch()).to_equal(true)
        expect(backend.supports_mouse()).to_equal(true)
        expect(backend.backend_name()).to_equal("tauri")
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### models iOS Tauri WebView as touch capable

- models iOS Tauri WebView as touch capable
   - Expected: has_capability(caps, Capability.Touch) is true
   - Expected: backend.supports_touch() is true
   - Expected: backend.supports_images() is true
   - Expected: backend.backend_name() equals `tauri`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models iOS Tauri WebView as touch capable")
val result = TauriBackend.new_ios(3000)
match result:
    Ok(backend) =>
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Touch)).to_equal(true)
        expect(backend.supports_touch()).to_equal(true)
        expect(backend.supports_images()).to_equal(true)
        expect(backend.backend_name()).to_equal("tauri")
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### has correct viewport

- has correct viewport
   - Expected: backend.viewport_width() equals `1280`
   - Expected: backend.viewport_height() equals `720`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct viewport")
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        expect(backend.viewport_width()).to_equal(1280)
        expect(backend.viewport_height()).to_equal(720)
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### initializes and shuts down

- initializes and shuts down
   - Expected: ok is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes and shuts down")
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        val init_result = backend.init()
        match init_result:
            Ok(ok) =>
                expect(ok).to_equal(true)
            Err(_) =>
                expect(false).to_equal(true)
        backend.shutdown()
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/tauri_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TauriBackend.
- TauriBackend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `1b6dcdab310bb2ac4603cd1a8a5945c8a3569a2db7dc7c424cd857f9c0b01b3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b6dcdab310bb2ac4603cd1a8a5945c8a3569a2db7dc7c424cd857f9c0b01b3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b6dcdab310bb2ac4603cd1a8a5945c8a3569a2db7dc7c424cd857f9c0b01b3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/ui/tauri_backend_spec.spl
mirror: doc/06_spec/unit/app/ui/tauri_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/tauri_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/tauri_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/tauri_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/tauri_backend_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/tauri_backend_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports correct capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/tauri_backend_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models Android Tauri WebView as touch capable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
