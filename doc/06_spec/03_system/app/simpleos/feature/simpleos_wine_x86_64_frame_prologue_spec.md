# Simpleos Wine X86 64 Frame Prologue Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_x86_64_frame_prologue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_x86_64_frame_prologue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_x86_64_frame_prologue_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_x86_64_frame_prologue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine X86 64 Frame Prologue Specification

## Scenarios

### SimpleOS Wine x86_64 frame prologue decode

### REQ-018: bounded known-console process dispatch plan

#### should classify frame-pointer prologue and epilogue forms before dispatch handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _frame_prologue_bytes()
expect(wine_x86_64_instruction_at(data, 0)).to_equal("push-rbp")
expect(wine_x86_64_instruction_len_at(data, 0)).to_equal(1)
expect(wine_x86_64_instruction_at(data, 1)).to_equal("mov-rbp-rsp")
expect(wine_x86_64_instruction_len_at(data, 1)).to_equal(3)
expect(wine_x86_64_instruction_at(data, 12)).to_equal("pop-rbp")
expect(wine_x86_64_instruction_len_at(data, 12)).to_equal(1)
val scan = wine_x86_64_scan_window(data, 0, 14, 8)
expect(scan.ok).to_equal(true)
expect(scan.state).to_equal("ready")
expect(scan.end_offset).to_equal(14)
expect(scan.instruction_count).to_equal(6)
expect(scan.last_offset).to_equal(13)
expect(scan.last_instruction).to_equal("ret")
```

</details>

#### should classify wide imm32 stack allocation before dispatch handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _wide_stack_frame_prologue_bytes()
expect(wine_x86_64_instruction_at(data, 4)).to_equal("sub-rsp-imm32")
expect(wine_x86_64_instruction_len_at(data, 4)).to_equal(7)
expect(wine_x86_64_instruction_at(data, 11)).to_equal("add-rsp-imm32")
expect(wine_x86_64_instruction_len_at(data, 11)).to_equal(7)
val scan = wine_x86_64_scan_window(data, 0, 20, 8)
expect(scan.ok).to_equal(true)
expect(scan.state).to_equal("ready")
expect(scan.end_offset).to_equal(20)
expect(scan.instruction_count).to_equal(6)
expect(scan.last_offset).to_equal(19)
expect(scan.last_instruction).to_equal("ret")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine x86_64 frame prologue decode
- REQ-018: bounded known-console process dispatch plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
