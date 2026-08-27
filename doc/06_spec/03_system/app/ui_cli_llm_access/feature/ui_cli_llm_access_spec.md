# UI CLI LLM Access

> Exercises the live T32-style access loop for Simple GUI/TUI and host-WM

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI CLI LLM Access

Exercises the live T32-style access loop for Simple GUI/TUI and host-WM

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the live T32-style access loop for Simple GUI/TUI and host-WM
surfaces through the canonical focused gate.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Screenshots | 3 |
| TUI Captures | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `protocol.json` | JSON artifact | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/protocol.json` |
| `tui-web.json` | JSON artifact | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/tui-web.json` |

### Screenshots

| Item | Kind | Path |
|------|------|------|
| `gui-before.png` | Screenshot | `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/gui-before.png` |
| `gui-after.png` | Screenshot | `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/gui-after.png` |
| `tui-web.png` | Screenshot | `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui-web.png` |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `` | TUI capture | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui/` |

## Scenarios

### UI CLI access for LLM operators
_Follow the same discover, inspect, find, act, and review-history grammar across T32 GUI access, Simple GUI/TUI sessions, and host WM windows. Primary scenarios show the operator flow; architecture, performance, and final gates remain folded._

<details>
<summary>Advanced: should register one shared T32, UI, and WM access grammar</summary>

#### should register one shared T32, UI, and WM access grammar

- should register one shared T32, UI, and WM access grammar
   - Protocol capture: after_step
- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should register one shared T32, UI, and WM access grammar")
step("Start UI access")
setup_ui_cli_access()
_check_gate("shared-grammar", [
    "AccessCommandDescriptor",
    "AccessOperation",
    "AccessRequest",
    "AccessResult",
    "AccessError",
    "AccessSafety",
    "AccessOutputMode",
    "sources=trace32,simple_ui,host_wm",
    "parity=list,capture_or_snapshot,find,act,history"
])
```

</details>


</details>

<details>
<summary>Advanced: should preserve T32 shared operations while mapping them to the common grammar</summary>

#### should preserve T32 shared operations while mapping them to the common grammar

- should preserve T32 shared operations while mapping them to the common grammar
   - Protocol capture: after_step
- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve T32 shared operations while mapping them to the common grammar")
step("Start UI access")
_check_gate("t32-compatibility", [
    "t32_shared_operations=preserved",
    "descriptor_mapping=pass",
    "operation_mapping=pass",
    "result_mapping=pass",
    "error_mapping=pass",
    "safety_mapping=pass",
    "output_mapping=pass",
    "history_request_id=pass",
    "t32_process_argv=pass",
    "t32_shell_concat=0",
    "t32_human_json_list_fields=equal"
])
```

</details>


</details>

#### should complete the live TUI discovery and safe-action loop

- should complete the live TUI discovery and safe-action loop
   - TUI capture: after_step
- Start UI access
   - TUI capture: after_step
- List active windows
   - TUI capture: after_step
- Inspect TUI rendering
   - TUI capture: after_step
- Find an interactive target
   - TUI capture: after_step
- Act on the target
   - TUI capture: after_step
- Review access history
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should complete the live TUI discovery and safe-action loop")
step("Start UI access")
step("List active windows")
step("Inspect TUI rendering")
step("Find an interactive target")
step("Act on the target")
step("Review access history")
_check_gate("live-tui-loop", [
    "source=simple_ui",
    "surface_kind=tui",
    "canonical_id=",
    "stale_revision=stale_target",
    "action_result=ok",
    "history_correlation=pass",
    "capture_kind=tui"
])
```

</details>

#### should complete the live GUI discovery and safe-action loop

- should complete the live GUI discovery and safe-action loop
   - GUI capture: after_step (HTML preferred when available)
- Start UI access
   - GUI capture: after_step (HTML preferred when available)
- List active windows
   - GUI capture: after_step (HTML preferred when available)
- Inspect GUI rendering
   - GUI capture: after_step (HTML preferred when available)
- Find an interactive target
   - GUI capture: after_step (HTML preferred when available)
- Act on the target
   - GUI capture: after_step (HTML preferred when available)
- Review access history
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should complete the live GUI discovery and safe-action loop")
step("Start UI access")
step("List active windows")
step("Inspect GUI rendering")
step("Find an interactive target")
step("Act on the target")
step("Review access history")
_check_gate("live-gui-loop", [
    "source=simple_ui",
    "surface_kind=gui",
    "canonical_id=",
    "stale_revision=stale_target",
    "action_result=ok",
    "history_correlation=pass",
    "capture_kind=gui"
])
```

</details>

#### should list and safely act on one normalized root per live host-WM window

- should list and safely act on one normalized root per live host-WM window
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step
- Review access history
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should list and safely act on one normalized root per live host-WM window")
step("List active windows")
step("Find an interactive target")
step("Act on the target")
step("Review access history")
_check_gate("live-wm-loop", [
    "source=host_wm",
    "shared_schema_fields=pass",
    "one_host_root_per_owner_window=true",
    "empty_windows=pass",
    "missing_target=target_not_found",
    "generation_guard=pass",
    "focused_surface=pass",
    "no_synthetic_focus=pass",
    "geometry_preserved=pass",
    "target_scoped_literal_type=pass",
    "macos_stable_identity=pass",
    "owner_adapter_action=pass",
    "history_correlation=pass"
])
```

</details>

<details>
<summary>Advanced: should preserve stable scoped identity, stale metadata, and removed-target rejection</summary>

#### should preserve stable scoped identity, stale metadata, and removed-target rejection

- should preserve stable scoped identity, stale metadata, and removed-target rejection
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve stable scoped identity, stale metadata, and removed-target rejection")
step("List active windows")
step("Find an interactive target")
step("Act on the target")
_check_gate("identity-ordering-staleness", [
    "stable_identity=pass",
    "deterministic_order=pass",
    "unavailable_fields=explicit",
    "removed_target=target_not_found",
    "reused_target=stale_target",
    "stale_metadata=true"
])
```

</details>


</details>

#### should preserve fixture fields and UTF-8 across human and versioned JSON output

- should preserve fixture fields and UTF-8 across human and versioned JSON output
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve fixture fields and UTF-8 across human and versioned JSON output")
step("List active windows")
_check_gate("output-modes", [
    "human_json_fixture_fields=equal",
    "human_json_required_fields=equal",
    "utf8_fields=preserved",
    "json_single_line=true",
    "schema_version=1",
    "ordering=deterministic",
    "truncation=explicit"
])
```

</details>

#### should map every stable code and serialize invalid arguments through typed error JSON

- should map every stable code and serialize invalid arguments through typed error JSON
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should map every stable code and serialize invalid arguments through typed error JSON")
step("Find an interactive target")
step("Act on the target")
_check_gate("error-taxonomy", [
    "source_unavailable",
    "interaction_required",
    "permission_denied",
    "unsupported_action",
    "target_not_found",
    "stale_target",
    "target_disabled",
    "target_busy",
    "timeout",
    "invalid_argument",
    "post_dispatch_timeout_correlation=pass",
    "typed_error_json=pass"
])
```

</details>

<details>
<summary>Advanced: should distinguish empty, headless, unavailable, and unsupported states</summary>

#### should distinguish empty, headless, unavailable, and unsupported states

- should distinguish empty, headless, unavailable, and unsupported states
   - Protocol capture: after_step
- Start UI access
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should distinguish empty, headless, unavailable, and unsupported states")
step("Start UI access")
step("List active windows")
_check_gate("environment-states", [
    "zero_windows=empty",
    "headless=headless",
    "backend_unavailable=source_unavailable",
    "unsupported_action=unsupported_action"
])
```

</details>


</details>

#### should enforce capability, state, coordinate, and confirmation safety

- should enforce capability, state, coordinate, and confirmation safety
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step
- Review access history
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce capability, state, coordinate, and confirmation safety")
step("Find an interactive target")
step("Act on the target")
step("Review access history")
_check_gate("action-safety", [
    "queried_target_used=true",
    "capability_checked=true",
    "state_checked=true",
    "untargeted_desktop_actions=rejected",
    "confirmation_required=true",
    "correlated_result=true"
])
```

</details>

<details>
<summary>Advanced: should delegate grammar, query, rendering, and safety to common owners</summary>

#### should delegate grammar, query, rendering, and safety to common owners

- should delegate grammar, query, rendering, and safety to common owners
   - Protocol capture: after_step
- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should delegate grammar, query, rendering, and safety to common owners")
step("Start UI access")
_check_gate("common-ownership", [
    "common_delegation_calls=pass",
    "frontend_owner_redefinitions=0",
    "common_host_backend_imports=0",
    "raw_runtime_string_guard=pass",
    "renderer_ir_string_guard=pass",
    "compiled_backend_routing_contract=pass",
    "installed_path_fallback_contract=pass",
    "raw_backend_source_exec=0"
])
```

</details>


</details>

<details>
<summary>Advanced: should bound history and reject selected subprocess and retry-sleep hot paths</summary>

#### should bound history and reject selected subprocess and retry-sleep hot paths

- should bound history and reject selected subprocess and retry-sleep hot paths
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step
- Inspect TUI rendering
   - Protocol capture: after_step
- Inspect GUI rendering
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound history and reject selected subprocess and retry-sleep hot paths")
step("List active windows")
step("Inspect TUI rendering")
step("Inspect GUI rendering")
step("Find an interactive target")
_check_gate("bounded-hot-paths", [
    "memory_history_limit=64",
    "persisted_history_limit=64",
    "ui_subprocess_calls=0",
    "wm_subprocess_per_record=0",
    "retry_sleeps=0"
])
```

</details>


</details>

<details>
<summary>Advanced: should meet warm latency and RSS targets with reproducible evidence</summary>

#### should meet warm latency and RSS targets with reproducible evidence

- should meet warm latency and RSS targets with reproducible evidence
   - Protocol capture: after_step
- Start UI access
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should meet warm latency and RSS targets with reproducible evidence")
step("Start UI access")
step("List active windows")
step("Find an interactive target")
_check_gate("performance", [
    "fixture_windows=100",
    "fixture_nodes=1000",
    "warm=true",
    "list_result_p95_ms<=100",
    "find_nodes_p95_ms<=20",
    "rss_delta_mib<=20",
    "p50_ms=",
    "p95_ms=",
    "max_rss_mib=",
    "output_checksum="
])
```

</details>


</details>

#### should keep shared descriptors and established command spellings compatible

- should keep shared descriptors and established command spellings compatible
   - TUI capture: after_step
- Start UI access
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep shared descriptors and established command spellings compatible")
step("Start UI access")
_check_gate("compatibility-help", [
    "simple_ui_operations=windows,snapshot,surface,find,act,history",
    "wm_descriptors=present",
    "existing_spellings=preserved",
    "unknown_command=invalid_argument",
    "t32_mapping_checked=true",
    "schema_v1_render=pass"
])
```

</details>

#### should reach live GUI and TUI sessions through the existing test API

- should reach live GUI and TUI sessions through the existing test API
   - Protocol capture: after_step
- Start UI access
   - Protocol capture: after_step
- Inspect TUI rendering
   - Protocol capture: after_step
- Inspect GUI rendering
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reach live GUI and TUI sessions through the existing test API")
step("Start UI access")
step("Inspect TUI rendering")
step("Inspect GUI rendering")
step("Act on the target")
_check_gate("live-ui-transport", [
    "runtime=pure-simple-self-hosted",
    "runtime_probe=pass",
    "runtime_provenance=pass",
    "rust_seed_used=false",
    "compiled_backend_artifact=pass",
    "gui_backend_route=simple-ui-gui",
    "tui_web_backend_route=simple-ui-tui_web",
    "t32_deployed_route=pass",
    "t32_invalid_json=invalid_argument",
    "t32_live_windows=pass",
    "t32_live_show=pass",
    "t32_live_describe=pass",
    "t32_live_action=pass",
    "t32_live_history=pass",
    "transport=existing-test-api",
    "client_process=separate",
    "loopback_default=true",
    "help_operations=pass",
    "human_json_fixture_fields=equal",
    "human_json_required_fields=equal",
    "gui_screenshot_dimensions=1280x800",
    "gui_screenshot_nonblank=pass",
    "gui_semantic_delta=unfocused_to_focused",
    "malformed_args=invalid_argument",
    "unknown_target=target_not_found",
    "live_windows=pass",
    "live_find=pass",
    "live_act=pass",
    "post_action_state=pass",
    "correlated_history=pass",
    "service_stop=source_unavailable",
    "db_fallback=read_only",
    "db_act=source_unavailable",
    "tui_web_transport=separate_process",
    "tui_web_html=visible",
    "tui_web_screenshot_dimensions=1280x800",
    "tui_web_screenshot_nonblank=pass",
    "tui_web_windows=pass",
    "tui_web_snapshot=pass",
    "tui_web_surface=pass",
    "tui_web_find=pass",
    "tui_web_act=pass",
    "tui_web_post_action_state=pass",
    "tui_web_correlated_history=pass",
    "tui_web_request_id=present"
])
```

</details>

<details>
<summary>Advanced: should produce manual-quality typed evidence with real assertions</summary>

#### should produce manual-quality typed evidence with real assertions

- should produce manual-quality typed evidence with real assertions
   - Protocol capture: after_step
- Inspect TUI rendering
   - Protocol capture: after_step
- Inspect GUI rendering
   - Protocol capture: after_step
- Review access history
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce manual-quality typed evidence with real assertions")
step("Inspect TUI rendering")
step("Inspect GUI rendering")
step("Review access history")
_check_gate("manual-evidence", [
    "capture_kind=tui",
    "capture_kind=gui",
    "capture_kind=protocol",
    "manual_steps=7",
    "manual_source_fresh=pass",
    "capture_links=pass",
    "placeholder_passes=0"
])
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `53dbae94886a9a502d892f3b3309a229a97242b46ae1162b46f9f28cab6e53b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53dbae94886a9a502d892f3b3309a229a97242b46ae1162b46f9f28cab6e53b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53dbae94886a9a502d892f3b3309a229a97242b46ae1162b46f9f28cab6e53b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl
mirror: doc/06_spec/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should register one shared T32, UI, and WM access grammar' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve T32 shared operations while mapping them to the common grammar' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve T32 shared operations while mapping them to the common grammar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should complete the live TUI discovery and safe-action loop' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should complete the live GUI discovery and safe-action loop' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:137:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should list and safely act on one normalized root per live host-WM window' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should list and safely act on one normalized root per live host-WM window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:162:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve stable scoped identity, stale metadata, and removed-target rejection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve stable scoped identity, stale metadata, and removed-target rejection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
