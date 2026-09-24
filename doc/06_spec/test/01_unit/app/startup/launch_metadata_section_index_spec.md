# Launch Metadata Section Index Specification

> Tests covering:

## Scenarios

### Launch metadata section validation [importance=critical; importance_weight=3]

### LM-A01: exact fail-fast precedence [importance=critical; importance_weight=3]

#### should accept out-of-order non-overlapping spans and half-open adjacency [importance=critical; importance_weight=3]

- Build a retained SMF with ordered section rows
- Validate retained metadata through the public entry point
- Compare the complete retained result with the compatibility oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a retained SMF with ordered section rows")
val payload = canonical_payload()
val rows = valid_metadata_rows()
step("Validate retained metadata through the public entry point")
val bytes = smf_fixture(rows, payload)
step("Compare the complete retained result with the compatibility oracle")
expect_retained(bytes, true, true, "smf", "launch_metadata_retained")
```

</details>

#### should reject an overlap before a later invalid alignment [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SectionRow(section_type: 1, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 4, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 5, size: 1, alignment: 3)
]
expect_retained(smf_fixture(rows, [], false, 16), true, false, "smf",
    "launch_metadata_section_overlap")
```

</details>

#### should report alignment before a same-row overlap when no prior overlap exists [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SectionRow(section_type: 1, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 4, size: 8, alignment: 3)
]
expect_retained(smf_fixture(rows, []), true, false, "smf",
    "launch_metadata_section_alignment_invalid")
```

</details>

#### should report overlap before a later invalid payload range [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SectionRow(section_type: 1, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 4, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 100000, size: 1, alignment: 16)
]
expect_retained(smf_fixture(rows, [], false, 16), true, false, "smf",
    "launch_metadata_section_overlap")
```

</details>

#### should report symbol-table overlap before decoding any section row [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [SectionRow(section_type: 15, offset: 0,
    size: canonical_payload().len(), alignment: 16)]
expect_retained(smf_fixture(rows, canonical_payload(), true), false, false,
    "smf", "launch_metadata_symbol_table_overlap")
```

</details>

### LM-A02: duplicate, zero-size, and overlap matrix [importance=critical; importance_weight=3]

#### should allow adjacent spans but reject equal-start and nested spans [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adjacent = [
    SectionRow(section_type: 1, offset: 0, size: 4, alignment: 16),
    SectionRow(section_type: 1, offset: 4, size: 4, alignment: 16)
]
expect_retained(smf_fixture(adjacent, []), false, true, "smf",
    "launch_metadata_absent")
val equal_start = [
    SectionRow(section_type: 1, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 0, size: 1, alignment: 16)
]
expect_retained(smf_fixture(equal_start, []), true, false, "smf",
    "launch_metadata_section_overlap")
val nested = [
    SectionRow(section_type: 1, offset: 0, size: 16, alignment: 16),
    SectionRow(section_type: 1, offset: 4, size: 2, alignment: 16)
]
expect_retained(smf_fixture(nested, []), true, false, "smf",
    "launch_metadata_section_overlap")
```

</details>

#### should let same-row overlap win over duplicate metadata [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SectionRow(section_type: 15, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 15, offset: 4, size: 8, alignment: 16)
]
expect_retained(smf_fixture(rows, canonical_payload()), true, false, "smf",
    "launch_metadata_section_overlap")
```

</details>

#### should report a non-overlapping duplicate metadata row [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SectionRow(section_type: 15, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 15, offset: 8, size: 8, alignment: 16)
]
expect_retained(smf_fixture(rows, canonical_payload()), true, false, "smf",
    "launch_metadata_section_duplicate")
```

</details>

#### should report zero-size metadata as payload-invalid without overlap [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [SectionRow(section_type: 15, offset: 0, size: 0, alignment: 16)]
expect_retained(smf_fixture(rows, []), true, false, "smf",
    "launch_metadata_payload_invalid")
```

</details>

#### should report an earlier overlap before a later zero-size metadata row [importance=critical; importance_weight=3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    SectionRow(section_type: 1, offset: 0, size: 8, alignment: 16),
    SectionRow(section_type: 1, offset: 4, size: 8, alignment: 16),
    SectionRow(section_type: 15, offset: 12, size: 0, alignment: 16)
]
expect_retained(smf_fixture(rows, [], false, 16), true, false, "smf",
    "launch_metadata_section_overlap")
```

</details>

### LM-A03: wide valid tables and exact byte oracle [importance=high; importance_weight=2]

#### should validate 64 and 256 non-overlapping section rows [importance=high; importance_weight=2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_retained(wide_valid_fixture(64), false, true, "smf",
    "launch_metadata_absent")
expect_retained(wide_valid_fixture(256), false, true, "smf",
    "launch_metadata_absent")
```

</details>

#### should validate 1024 and 4096 non-overlapping section rows [importance=high; importance_weight=2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_retained(wide_valid_fixture(1024), false, true, "smf",
    "launch_metadata_absent")
expect_retained(wide_valid_fixture(4096), false, true, "smf",
    "launch_metadata_absent")
```

</details>

#### should preserve a byte-exact retained payload result [importance=high; importance_weight=2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = canonical_payload()
val rows = valid_metadata_rows()
val result = retained_smf_launch_metadata_v1(smf_fixture(rows, payload), "smf")
expect(result.present).to_equal(true)
expect(result.ok).to_equal(true)
expect(result.reason).to_equal("launch_metadata_retained")
expect(render_launch_metadata_sidecar(result.metadata)).to_equal(
    "simple_launch_metadata:\n" +
    "  entry_kind: \"smf\"\n" +
    "  target_os: \"\"\n" +
    "  target_arch: \"\"\n" +
    "  target_abi: \"\"\n" +
    "  uses_arg_parser: true\n" +
    "  mmap_hint: true\n" +
    "  load_policy: \"map_selected_segments\"\n")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/launch_metadata_section_index_spec.spl` |
| Updated | 2026-09-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Launch metadata section validation [importance=critical; importance_weight=3]
- LM-A01: exact fail-fast precedence [importance=critical; importance_weight=3]
- LM-A02: duplicate, zero-size, and overlap matrix [importance=critical; importance_weight=3]
- LM-A03: wide valid tables and exact byte oracle [importance=high; importance_weight=2]

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


<!-- sdn-diagram:id=launch_metadata_section_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=launch_metadata_section_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

launch_metadata_section_index_spec -> std
launch_metadata_section_index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=launch_metadata_section_index_spec.arch hash=sha256:auto
+-----+      +------------------------------------+
| app | ---> | launch_metadata_section_index_spec |
+-----+      +------------------------------------+
             +------------------------------------+
             | std                                |
             +------------------------------------+
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |
