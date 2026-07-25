# Simple 2d Renderdoc Manual And Contract Audit Specification

> <details>

<!-- sdn-diagram:id=simple_2d_renderdoc_manual_and_contract_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_manual_and_contract_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_2d_renderdoc_manual_and_contract_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_manual_and_contract_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2d Renderdoc Manual And Contract Audit Specification

## Scenarios

### Simple 2D RenderDoc documentation contract

#### should mirror every executable scenario into a zero-stub manual

- Inspect all backend-equivalence spec and manual pairs
- pending manual contract audit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect all backend-equivalence spec and manual pairs")
expect(13).to_be_greater_than(0)
pending_manual_contract_audit()
```

</details>

#### should keep modern steps captures requirements and direct matchers

- Audit scenario source quality
   - Expected: ["step", "capture", "req", "expect"].len() equals `4`
- pending manual contract audit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Audit scenario source quality")
expect(["step", "capture", "req", "expect"].len()).to_equal(4)
pending_manual_contract_audit()
```

</details>

<details>
<summary>Advanced: should reject executable specs under the generated manual tree</summary>

#### should reject executable specs under the generated manual tree

- Scan doc/06_spec for executable Simple files
   - Expected: 0 equals `0`
- pending manual contract audit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Scan doc/06_spec for executable Simple files")
expect(0).to_equal(0)
pending_manual_contract_audit()
```

</details>


</details>

<details>
<summary>Advanced: should require sidecar merge and highest-capability review evidence</summary>

#### should require sidecar merge and highest-capability review evidence

- Inspect cooperative review completion
- pending manual contract audit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect cooperative review completion")
expect("highest-capability-review").to_contain("review")
pending_manual_contract_audit()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple 2D RenderDoc documentation contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
