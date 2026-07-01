# Mcp T32 State Diff Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_state_diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_state_diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_state_diff_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_state_diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 State Diff Specification

## Scenarios

### T32 MCP State Diff

#### identical states

#### returns empty diff for identical states

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state1 = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|12345", "break_list|67890"],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val state2 = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|12345", "break_list|67890"],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val changes = diff_states(state1, state2)
expect(changes.len()).to_equal(0)
```

</details>

#### changed states

#### detects changed register_view window

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|111"],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val after = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|222"],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val changes = diff_states(before, after)
expect(changes.len()).to_equal(1)
expect(changes[0]).to_equal("window:register_view")
```

</details>

#### detects changed PC register

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = TestStepState(
    session_id: "t32_1",
    window_snapshots: [],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val after = TestStepState(
    session_id: "t32_1",
    window_snapshots: [],
    register_pc: "0x08001238",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val changes = diff_states(before, after)
expect(changes.len()).to_equal(1)
expect(changes[0]).to_equal("reg:PC")
```

</details>

#### detects multiple changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|111", "break_list|222"],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val after = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|999", "break_list|222"],
    register_pc: "0x08001238",
    register_sp: "0x20001000",
    register_lr: "0x08000200"
)
val changes = diff_states(before, after)
expect(changes.len()).to_equal(3)
```

</details>

#### missing snapshots

#### treats missing before as changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = TestStepState(
    session_id: "t32_1",
    window_snapshots: [],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val after = TestStepState(
    session_id: "t32_1",
    window_snapshots: ["register_view|111"],
    register_pc: "0x08001234",
    register_sp: "0x20001000",
    register_lr: "0x08000100"
)
val changes = diff_states(before, after)
expect(changes.len()).to_equal(1)
expect(changes[0]).to_equal("window:register_view")
```

</details>

#### simple hash

#### produces consistent hash for same content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = simple_hash("hello")
val h2 = simple_hash("hello")
expect(h1).to_equal(h2)
```

</details>

#### produces different hash for different content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = simple_hash("hello")
val h2 = simple_hash("world")
expect(h1 == h2).to_equal(false)
```

</details>

#### step history capping

#### history array grows with push

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_history_grows()
expect(result[0]).to_equal(3)
expect(result[1]).to_equal(1)
```

</details>

#### capping logic keeps tail

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trimmed = test_capping_logic()
expect(trimmed.len()).to_equal(3)
expect(trimmed[0]).to_equal("c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_state_diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP State Diff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
