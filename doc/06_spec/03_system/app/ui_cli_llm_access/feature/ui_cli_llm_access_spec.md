# Ui Cli Llm Access Specification

> _Follow the same discover, inspect, find, act, and review-history grammar across T32 GUI access, Simple GUI/TUI sessions, and host WM windows. Primary scenarios show the operator flow; architecture, performance, and final gates remain folded._

<!-- sdn-diagram:id=ui_cli_llm_access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_cli_llm_access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_cli_llm_access_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_cli_llm_access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Cli Llm Access Specification

## Evidence

Display policy: `embed_tui`

The final gate parses the runtime receipt, semantic before/after state, TRACE32
font/RCL/window-tree status, and screenshot pixels before accepting these
captures. Missing or stale files fail closed.

| Item | Kind | Path |
|------|------|------|
| `tui/` | TUI captures | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui/` |
| `protocol.json` | GUI protocol | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/protocol.json` |
| `tui-web.json` | TUI-web protocol | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/tui-web.json` |
| `t32-gui-status.txt` | TRACE32 status | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/t32/t32-gui-status.txt` |
| `t32-gui.png` | TRACE32 GUI | `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/t32/t32-gui.png` |
| `gui-before.png` | GUI before action | `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/gui-before.png` |
| `gui-after.png` | GUI after action | `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/gui-after.png` |
| `tui-web.png` | TUI-web rendering | `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui-web.png` |

## Scenarios

### UI CLI access for LLM operators
_Follow the same discover, inspect, find, act, and review-history grammar across T32 GUI access, Simple GUI/TUI sessions, and host WM windows. Primary scenarios show the operator flow; architecture, performance, and final gates remain folded._

<details>
<summary>Advanced: should register one shared T32, UI, and WM access grammar</summary>

#### should register one shared T32, UI, and WM access grammar

- Start UI access
   - Protocol capture: after_step
- setup ui cli access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- List active windows
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- List active windows
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Start UI access
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Find an interactive target
   - Protocol capture: after_step
- Act on the target
   - Protocol capture: after_step
- Review access history
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Start UI access
   - Protocol capture: after_step
- List active windows
   - Protocol capture: after_step
- Find an interactive target
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Start UI access
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect TUI rendering
   - Protocol capture: after_step
- Inspect GUI rendering
   - Protocol capture: after_step
- Review access history
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl` |
| Updated | 2026-07-13 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UI CLI access for LLM operators

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
