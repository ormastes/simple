# Regeneration Specification

> <details>

<!-- sdn-diagram:id=regeneration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=regeneration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

regeneration_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=regeneration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regeneration Specification

## Scenarios

### Lean Regeneration

#### module generators

#### regenerates async compile output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lean_code = regen_async.regenerate_async_compile()
expect(lean_code).to_contain("inductive Effect")
expect(lean_code).to_contain("theorem append_safe")
expect(lean_code).to_contain("theorem wait_detected")
expect(lean_code.contains("sorry")).to_equal(false)
```

</details>

#### regenerates GC borrow output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lean_code = regen_gc.regenerate_gc_manual_borrow()
expect(lean_code).to_contain("structure GcState")
expect(lean_code).to_contain("theorem borrow_preserves")
expect(lean_code).to_contain("theorem collect_preserves")
expect(lean_code.contains("sorry")).to_equal(false)
```

</details>

#### regenerates memory capability output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code).to_contain("inductive RefCapability")
expect(lean_code).to_contain("def canConvert")
expect(lean_code).to_contain("theorem conversion_is_safe")
```

</details>

#### regenerate_all

#### returns all expected file entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = regen.regenerate_all()
expect(files.len()).to_equal(15)
expect(files.has("src/verification/async_compile/src/AsyncCompile.lean")).to_equal(true)
expect(files.has("src/verification/gc_manual_borrow/src/GcManualBorrow.lean")).to_equal(true)

if files.has("src/verification/async_compile/src/AsyncCompile.lean"):
    val async_file = files.get("src/verification/async_compile/src/AsyncCompile.lean")
    expect(async_file.contains("theorem append_safe")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/regeneration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Regeneration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
