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
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Cli Llm Access Specification

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
<summary>Advanced: should preserve T32 commands while mapping overlapping operations</summary>

#### should preserve T32 commands while mapping overlapping operations

- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start UI access")
_check_gate("t32-compatibility", [
    "t32_specific_commands=preserved",
    "descriptor_mapping=pass",
    "operation_mapping=pass",
    "result_mapping=pass",
    "error_mapping=pass",
    "safety_mapping=pass",
    "output_mapping=pass"
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
    "action_result=ok",
    "history_correlation=pass",
    "capture_kind=gui"
])
```

</details>

#### should list and safely act on live host-WM windows

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
    "schema_parity=pass",
    "deterministic_order=pass",
    "top_level_only=true",
    "owner_adapter_action=pass",
    "history_correlation=pass"
])
```

</details>

<details>
<summary>Advanced: should preserve stable scoped identity and reject stale targets</summary>

#### should preserve stable scoped identity and reject stale targets

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
    "stale_response=stale_target"
])
```

</details>


</details>

#### should keep human and versioned JSON output semantically equal

- List active windows
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("List active windows")
_check_gate("output-modes", [
    "human_json_semantics=equal",
    "json_payload_count=1",
    "json_encoding=utf-8",
    "json_version=",
    "stdout_diagnostics=0",
    "ordering=deterministic",
    "truncation=explicit"
])
```

</details>

#### should return every stable access failure without fabrication

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
    "semantic_fallback=none",
    "fabricated_output=none"
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
    "unsupported_rendering=unsupported_action",
    "crash_count=0"
])
```

</details>


</details>

#### should enforce capability, state, input, timeout, and confirmation safety

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
    "target_reresolved=true",
    "capability_checked=true",
    "state_checked=true",
    "input_bounded=true",
    "timeout_enforced=true",
    "confirmation_policy=eligible",
    "silent_approval=false",
    "raw_input_fallback=false",
    "correlated_result=true"
])
```

</details>

<details>
<summary>Advanced: should keep snapshots, queries, serialization, safety, and history common-owned</summary>

#### should keep snapshots, queries, serialization, safety, and history common-owned

- Start UI access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start UI access")
_check_gate("common-ownership", [
    "cli_parallel_model=none",
    "normalization_owner=common",
    "query_owner=common",
    "serialization_owner=common",
    "safety_owner=common",
    "history_owner=common",
    "adapter_owned=enumerate,capture,refresh,act",
    "common_host_backend_imports=0",
    "raw_runtime_shortcuts=0"
])
```

</details>


</details>

<details>
<summary>Advanced: should keep bounded access hot paths free of scans and subprocess fanout</summary>

#### should keep bounded access hot paths free of scans and subprocess fanout

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
    "history_limit=64",
    "full_tree_scans=0",
    "source_reparses=0",
    "subprocess_per_record=0",
    "retry_sleeps=0",
    "cached_artifact_wrapper=pass",
    "dependency_light_grammar=pass"
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
    "list_snapshot_p95_ms<=100",
    "find_route_p95_ms<=20",
    "rss_delta_mib<=20",
    "p50_ms=",
    "p95_ms=",
    "max_rss_mib=",
    "output_checksum="
])
```

</details>


</details>

#### should keep help, deployed commands, and existing access surfaces compatible

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
    "wm_commands=live",
    "existing_spellings=preserved",
    "t32_mapping_documented=true",
    "existing_ui_modes=pass",
    "existing_play_commands=pass",
    "mcp_http_protocol=pass",
    "schema_additions=additive"
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
    "transport=existing-test-api",
    "client_process=separate",
    "loopback_default=true",
    "live_windows=pass",
    "live_find=pass",
    "live_act=pass",
    "post_action_state=pass",
    "correlated_history=pass",
    "service_stop=source_unavailable",
    "db_fallback=read_only",
    "db_act=source_unavailable"
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
    "placeholder_passes=0"
])
```

</details>


</details>

<details>
<summary>Advanced: should pass the converged focused gate and highest-capability review</summary>

#### should pass the converged focused gate and highest-capability review

- Start UI access
   - Protocol capture: after_step
- Review access history
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start UI access")
step("Review access history")
_check_gate("final", [
    "common_contract=pass",
    "cli_routing=pass",
    "ui_wm_parity=pass",
    "shared_grammar_parity=pass",
    "schema=pass",
    "safety=pass",
    "action_history=pass",
    "generated_manual=pass",
    "direct_runtime_guards=pass",
    "spec_layout_guard=pass",
    "highest_capability_review=accepted"
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
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
