# Simple Sdl3 Contract Specification

> Tests covering SDL3 canonical event backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Sdl3 Contract Specification

## Scenarios

### SDL3 canonical event backend

#### normalizes SDL3 modifier masks without reusing SDL2 event codes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes SDL3 modifier masks without reusing SDL2 event codes
   - Expected: sdl3_normalize_modifiers(1 | 64 | 256 | 1024) equals `15`
   - Expected: sdl3_normalize_modifiers(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes SDL3 modifier masks without reusing SDL2 event codes")
expect(sdl3_normalize_modifiers(1 | 64 | 256 | 1024)).to_equal(15)
expect(sdl3_normalize_modifiers(0)).to_equal(0)
```

</details>

#### dynamically loads SDL3 and fails closed without SDL2 substitution

- dynamically loads SDL3 and fails closed without SDL2 substitution
   - Expected: runtime does not contain `libSDL2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dynamically loads SDL3 and fails closed without SDL2 substitution")
val runtime = file_read("src/runtime/runtime_sdl3.c")
expect(runtime).to_contain("libSDL3.so.0")
expect(runtime).to_contain("SDL3.dll")
expect(runtime).to_contain("libSDL3.0.dylib")
expect(runtime).to_contain("SDL3_EVENT_KEY_DOWN UINT32_C(0x300)")
expect(runtime).to_contain("SDL3_EVENT_MOUSE_MOTION UINT32_C(0x400)")
expect(runtime.contains("libSDL2")).to_equal(false)
```

</details>

<details>
<summary>Advanced: routes SDL3 events through the same bounded WindowEventLoop as GLFW</summary>

#### routes SDL3 events through the same bounded WindowEventLoop as GLFW

- routes SDL3 events through the same bounded WindowEventLoop as GLFW


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes SDL3 events through the same bounded WindowEventLoop as GLFW")
val adapter = file_read("src/lib/nogc_sync_mut/io/simple_sdl3.spl")
expect(adapter).to_contain("events: WindowEventLoop")
expect(adapter).to_contain("self.events.enqueue_text")
expect(adapter).to_contain("self.events.enqueue_scalar")
expect(adapter).to_contain("self.events.drop_window_events")
```

</details>


</details>

#### ships both dynamic hosted backends in production native runtime bundles

- ships both dynamic hosted backends in production native runtime bundles


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ships both dynamic hosted backends in production native runtime bundles")
val compiler = file_read("src/compiler/70.backend/backend/runtime_compiler.spl")
expect(compiler).to_contain("\"runtime_glfw\"")
expect(compiler).to_contain("\"runtime_sdl3\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDL3 canonical event backend.
- SDL3 canonical event backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `95372e941d65d8b95d5e409b32c9a380aad36871f56737baa7ccd52662f8ca21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95372e941d65d8b95d5e409b32c9a380aad36871f56737baa7ccd52662f8ca21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95372e941d65d8b95d5e409b32c9a380aad36871f56737baa7ccd52662f8ca21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes SDL3 modifier masks without reusing SDL2 event codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dynamically loads SDL3 and fails closed without SDL2 substitution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/io/simple_sdl3_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes SDL3 events through the same bounded WindowEventLoop as GLFW' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
