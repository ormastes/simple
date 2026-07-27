# Simple 2d Renderdoc Manual And Contract Audit Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2d Renderdoc Manual And Contract Audit Specification

## Scenarios

### Simple 2D RenderDoc documentation contract

#### mirrors every executable scenario into an operator manual

- Inspect all backend-equivalence spec and manual pairs
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: SPECS.len() equals `MANUALS.len()`
   - Expected: SPECS.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect all backend-equivalence spec and manual pairs")
expect(SPECS.len()).to_equal(MANUALS.len())
expect(SPECS.len()).to_equal(13)
var index = 0
while index < SPECS.len():
    expect(file_exists(SPECS[index])).to_be(true)
    expect(file_exists(MANUALS[index])).to_be(true)
    expect(file_read(MANUALS[index]).len()).to_be_greater_than(0)
    val legacy = MANUALS[index].replace("doc/06_spec/", "doc/06_spec/test/")
    expect(file_exists(legacy)).to_be(true)
    expect(file_read(legacy).len()).to_be_greater_than(0)
    index = index + 1
```

</details>

#### keeps modern steps requirements direct matchers and no fail placeholders

- Audit scenario source quality
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: source contains `"expect(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Audit scenario source quality")
for path in SPECS:
    val source = file_read(path)
    expect(source).to_contain("# @req")
    expect(source).to_contain("step(")
    expect(source).to_contain("expect(")
    if path != "test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl":
        expect(source.contains("pass_todo")).to_be(false)
        expect(source.contains("expect(true).to_equal(true)")).to_be(false)
        expect(source.contains("pending_")).to_be(false)
```

</details>

<details>
<summary>Advanced: rejects executable specs under the generated manual tree</summary>

#### rejects executable specs under the generated manual tree

- Scan doc/06_spec for executable Simple files
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: code equals `0`
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Scan doc/06_spec for executable Simple files")
val (out, _err, code) = process_run(
    "/bin/sh", ["-c", "find doc/06_spec -name '*_spec.spl' -print"])
expect(code).to_equal(0)
expect(out).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: requires sidecar merge and highest-capability review ownership</summary>

#### requires sidecar merge and highest-capability review ownership

- Inspect cooperative review completion
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect cooperative review completion")
val plan = file_read(
    "doc/03_plan/agent_tasks/simple_2d_renderdoc_backend_equivalence.md")
expect(plan).to_contain("Merge owner: primary Codex `/root`")
expect(plan).to_contain("Final reviewer: highest available normal Codex")
expect(plan).to_contain("Generated-manual review owner: primary Codex")
expect(plan).to_contain("Sidecars were read-only design auditors")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl` |
| Updated | 2026-07-27 |
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
