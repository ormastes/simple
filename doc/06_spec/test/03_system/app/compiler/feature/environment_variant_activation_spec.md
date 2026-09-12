# Environment Variant Activation Specification

> Tests covering:

## Scenarios

### E5-003 integrated verification evidence [importance=high; importance_weight=2]

#### E5-003 should pass required compiler library MCP and LSP gates together [importance=high; importance_weight=2]

- Run the required compiler, library, MCP, and LSP gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-014
step("Run the required compiler, library, MCP, and LSP gates")
require_compiler_lib_mcp_lsp_gates()
```

</details>

#### E5-003 should reject a stale or stubbed generated manual [importance=high; importance_weight=2]

- Regenerate each manual and inspect its zero-stub receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-014
step("Regenerate each manual and inspect its zero-stub receipt")
require_zero_stub_manuals()
```

</details>

#### E5-003 should retain startup counters and warm performance evidence [importance=high; importance_weight=2]

- Capture startup probes, warm latency, RSS, and branch evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-013
# @req REQ-014
step("Capture startup probes, warm latency, RSS, and branch evidence")
require_startup_measurement_receipt()
```

</details>

### E5-004 canonical gap tracking [importance=high; importance_weight=2]

#### E5-004 should record every excluded architecture and device gap exactly once [importance=high; importance_weight=2]

- Allocate canonical feature and TODO rows for ARM, RISC-V, GPU, and x86-v4 gaps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-002
# @req REQ-011
step("Allocate canonical feature and TODO rows for ARM, RISC-V, GPU, and x86-v4 gaps")
require_gap_row_authority()
```

</details>

#### E5-004 should link existing open work without duplicate tracking IDs [importance=high; importance_weight=2]

- Reconcile existing x86, GPU, Vulkan, and backend TODO identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-014
step("Reconcile existing x86, GPU, Vulkan, and backend TODO identities")
require_gap_row_authority()
```

</details>

#### E5-004 should keep unqualified gaps pending rather than claiming completion [importance=high; importance_weight=2]

- Review pending state, evidence class, owner, and resume condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-014
step("Review pending state, evidence class, owner, and resume condition")
require_gap_row_authority()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/environment_variant_activation_spec.spl` |
| Updated | 2026-09-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- E5-003 integrated verification evidence [importance=high; importance_weight=2]
- E5-004 canonical gap tracking [importance=high; importance_weight=2]

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


<!-- sdn-diagram:id=environment_variant_activation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=environment_variant_activation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

environment_variant_activation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=environment_variant_activation_spec.arch hash=sha256:auto
+-------------------------------------+      +-----+
| environment_variant_activation_spec | ---> | std |
+-------------------------------------+      +-----+
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |
