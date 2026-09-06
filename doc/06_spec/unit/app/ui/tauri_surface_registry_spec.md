# Tauri Surface Registry Specification

> Tests covering app.ui.tauri.surface_registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Surface Registry Specification

## Scenarios

### app.ui.tauri.surface_registry

#### exposes a Tauri registry helper in the shared-WM Tauri entrypoint

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes a Tauri registry helper in the shared-WM Tauri entrypoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a Tauri registry helper in the shared-WM Tauri entrypoint")
val source = _source("src/app/ui.tauri/async_app.spl")
expect(source).to_contain("fn register_tauri_window")
expect(source).to_contain("UI_SURFACE_KIND_TAURI")
expect(source).to_contain("reg.bind_with_kind(window_id, surface_id, process_id, app_id, title, UI_SURFACE_KIND_TAURI)")
```

</details>

#### binds a Tauri window with the Tauri surface kind

- binds a Tauri window with the Tauri surface kind
   - Expected: binding.surface_kind equals `UI_SURFACE_KIND_TAURI`
   - Expected: reg.window_id_for_surface("surface-tauri") equals `window-tauri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a Tauri window with the Tauri surface kind")
val reg = new_ui_window_surface_registry()
_register_tauri_window(reg, "surface-tauri", "window-tauri", 77 as u64, "app.tauri", "Tauri")
val binding = reg.for_surface("surface-tauri")
expect(binding).to_not_equal(nil)
expect(binding.surface_kind).to_equal(UI_SURFACE_KIND_TAURI)
expect(reg.window_id_for_surface("surface-tauri")).to_equal("window-tauri")
```

</details>

#### replaces prior bindings through the shared one-to-one registry rule

- replaces prior bindings through the shared one-to-one registry rule
   - Expected: reg.len() equals `1`
   - Expected: reg.window_id_for_surface("surface-one") equals ``
   - Expected: reg.window_id_for_surface("surface-two") equals `window-tauri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces prior bindings through the shared one-to-one registry rule")
val reg = new_ui_window_surface_registry()
_register_tauri_window(reg, "surface-one", "window-tauri", 77 as u64, "app.tauri", "One")
_register_tauri_window(reg, "surface-two", "window-tauri", 77 as u64, "app.tauri", "Two")
expect(reg.len()).to_equal(1)
expect(reg.window_id_for_surface("surface-one")).to_equal("")
expect(reg.window_id_for_surface("surface-two")).to_equal("window-tauri")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/tauri_surface_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app.ui.tauri.surface_registry.
- app.ui.tauri.surface_registry

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d88733b2f64bd7a769668a5a2cd0aa13d2c58cceed8fb49e97a3fd60c208d914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d88733b2f64bd7a769668a5a2cd0aa13d2c58cceed8fb49e97a3fd60c208d914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d88733b2f64bd7a769668a5a2cd0aa13d2c58cceed8fb49e97a3fd60c208d914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/ui/tauri_surface_registry_spec.spl
mirror: doc/06_spec/unit/app/ui/tauri_surface_registry_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/tauri_surface_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/tauri_surface_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/tauri_surface_registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/tauri_surface_registry_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes a Tauri registry helper in the shared-WM Tauri entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/tauri_surface_registry_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds a Tauri window with the Tauri surface kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/tauri_surface_registry_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces prior bindings through the shared one-to-one registry rule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
