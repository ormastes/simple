# Html Ui Payload Specification

> <details>

<!-- sdn-diagram:id=html_ui_payload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_ui_payload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_ui_payload_spec -> std
html_ui_payload_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_ui_payload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Ui Payload Specification

## Scenarios

### html ui payload helpers

#### round trips ASCII payloads through base64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = payload_encode("hello")
expect(encoded).to_equal("aGVsbG8=")
expect(payload_decode(encoded)).to_equal("hello")
```

</details>

#### splits payloads without changing chunk order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = payload_split("abcdefghijkl", 5)
expect(chunks.len()).to_equal(3)
expect(chunks[0]).to_equal("abcde")
expect(chunks[1]).to_equal("fghij")
expect(chunks[2]).to_equal("kl")
```

</details>

#### generates std module source with embedded html and css payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = gen_std_module_source("page", "HTML", ["CSS"])
expect(src).to_contain("# Generated std UI module: page")
expect(src).to_contain("fn ui_html_b64() -> text:")
expect(src).to_contain("    \"HTML\"")
expect(src).to_contain("fn ui_css_b64(idx: i64) -> text:")
expect(src).to_contain("    if idx == 0:")
expect(src).to_contain("        \"CSS\"")
expect(src).to_contain("export ui_css_b64")
```

</details>

#### generates dyn main source with part lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = UiPartMap(tags: ["button", "input"], parts: ["page_part_0.smf", "page_part_1.smf"])
val src = gen_dyn_main_source("page", map, "", [])
expect(src).to_contain("# Generated dyn main UI module: page")
expect(src).to_contain("\"button\",")
expect(src).to_contain("\"input\"")
expect(src).to_contain("fn ui_part_for(tag: text) -> text:")
expect(src).to_contain("    if tag == \"button\":")
expect(src).to_contain("        \"page_part_0.smf\"")
expect(src).to_contain("    else if tag == \"input\":")
expect(src).to_contain("        \"page_part_1.smf\"")
expect(src).to_contain("export ui_part_for")
```

</details>

#### generates dyn part source with the payload literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = gen_dyn_part_source("page", 2, "PAYLOAD")
expect(src).to_contain("# Generated dyn part module: page_part_2")
expect(src).to_contain("fn ui_part_payload() -> text:")
expect(src).to_contain("    \"PAYLOAD\"")
expect(src).to_contain("export ui_part_payload")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/html_ui_payload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html ui payload helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
