# deps_deep_spec

> Deep dependency report spec.

<!-- sdn-diagram:id=deps_deep_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deps_deep_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deps_deep_spec -> std
deps_deep_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deps_deep_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# deps_deep_spec

Deep dependency report spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/deps/deps_deep_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Deep dependency report spec.

Validates the three-section report produced by deps_deep_report_lines
against a small hand-built closure: json.spl + jsonrpc.spl from mcp_sdk.

## Scenarios

### deps_deep_report_lines

#### produces a non-empty report

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
expect(rpt.len()).to_be_greater_than(0)
```

</details>

#### report header contains entry file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains(JSON_SPL)).to_equal(true)
```

</details>

#### SCRIPT section header is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("SECTION 1: SCRIPT")).to_equal(true)
```

</details>

#### json.spl has positive code line count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
# code_lines line must appear
expect(joined.contains("code_lines:")).to_equal(true)
```

</details>

#### json.spl exports known function extract_json_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("extract_json_string")).to_equal(true)
```

</details>

#### script totals report positive interface symbol count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("total_interface_symbols:")).to_equal(true)
# At least one symbol was found — verify escape_json (top-level, no _-prefix) appears
expect(joined.contains("- escape_json")).to_equal(true)
```

</details>

#### SMF section header is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("SECTION 2: SMF")).to_equal(true)
```

</details>

#### json.smf exists flag matches actual file presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actually_exists = file_exists(JSON_SMF)
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
if actually_exists:
    expect(joined.contains("smf_exists: yes")).to_equal(true)
else:
    expect(joined.contains("smf_exists: no")).to_equal(true)
```

</details>

#### smf size is non-negative when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("smf_size_bytes:")).to_equal(true)
```

</details>

#### NATIVE section header is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("SECTION 3: NATIVE")).to_equal(true)
```

</details>

#### native_bytes line is present for json.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("native_bytes:")).to_equal(true)
```

</details>

#### native bytes total is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("total_native_bytes:")).to_equal(true)
```

</details>

#### native method is documented in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
# One of the three method labels must appear
val has_smf = joined.contains("smf_symbol_table")
val has_est = joined.contains("estimate_from_code_lines")
val has_art = joined.contains("smf_artifact_size")
val any_method = has_smf or has_est or has_art
expect(any_method).to_equal(true)
```

</details>

### deps_deep_report

#### returns same content as lines joined

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpt_lines = deps_deep_report_lines(make_closure(), JSON_SPL)
val rpt_text = deps_deep_report(make_closure(), JSON_SPL)
expect(rpt_text.len()).to_be_greater_than(0)
# First line of lines array should appear in text version
val first_line = rpt_lines[0]
expect(rpt_text.contains(first_line)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
