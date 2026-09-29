# Browser Cdp Debug Contract Slice Specification

> Tests covering REQ-015 browser JS Wasm debug contract slice.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Cdp Debug Contract Slice Specification

## Scenarios

### REQ-015 browser JS Wasm debug contract slice

#### reports this host truthfully when no reachable browser executable exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (path, _stderr, _code) = rt_process_run("/bin/sh", ["-c", "command -v chromium || command -v chromium-browser || command -v google-chrome || command -v electron || true"])
expect(path.trim()).to_equal("")
val slice = browser_cdp_blocked_v1("build-browser-system-host", debug_policy_observe_only_v1(), "no Chromium, Chrome, or Electron executable found on this host").unwrap()
val graph = central_debug_service_v1_graph(slice.session_id).unwrap()
expect(graph.build_id).to_equal("build-browser-system-host")
expect(graph.capabilities.all(\cap: cap.support == CapLevel.Unavailable and cap.verification == DebugVerificationV1.Blocked)).to_equal(true)
expect(slice.worker_auto_attach_verified).to_equal(false)
expect(slice.boundary_frames.len()).to_equal(0)
expect(slice.source_mapping_reason).to_contain("blocked")
expect(central_debug_service_v1_receipts(slice.session_id).last().reason).to_contain("redacted")
central_debug_service_v1_close(slice.session_id).unwrap()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_cdp_debug_contract_slice_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-015 browser JS Wasm debug contract slice.
- REQ-015 browser JS Wasm debug contract slice

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
