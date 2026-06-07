# test_mir_parse_spec

> Generates SPIR-V code for Vulkan compute shaders.

<!-- sdn-diagram:id=test_mir_parse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_mir_parse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_mir_parse_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_mir_parse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_mir_parse_spec

Generates SPIR-V code for Vulkan compute shaders.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/test_mir_parse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Generates SPIR-V code for Vulkan compute shaders.

    SPIR-V is a binary format, but we generate human-readable
    assembly that can be assembled with spirv-as or used for debugging.

    Structure:
    1. Capabilities and extensions
    2. Memory model
    3. Entry point declaration
    4. Decorations
    5. Type declarations
    6. Constants
    7. Global variables
    8. Functions

    This builder generates SPIR-V assembly (text) that can be
    assembled to binary using spirv-as from SPIRV-Tools.

## Scenarios

### parse test

#### loads

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
