# Tmp Html Compat Core Native Specification

> <details>

<!-- sdn-diagram:id=tmp_html_compat_core_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_html_compat_core_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_html_compat_core_native_spec -> std
tmp_html_compat_core_native_spec -> common
tmp_html_compat_core_native_spec -> gc_async_mut
tmp_html_compat_core_native_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_html_compat_core_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Html Compat Core Native Specification

## Scenarios

### html compat core native

#### renders core boxes without the compare bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = html_compat_fixture_simple_boxes("24_flex_wrap_reverse_basic", 320, 240)
expect(boxes.len()).to_equal(4)
expect(boxes[0].label).to_equal("wrap_reverse_shell")
expect(boxes[1].y).to_equal(40)
```

</details>

#### emits nonzero draw IR for section with h3 and p children

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = file_read("test/fixtures/html_compat/06_card_panel.html")
expect(html.len()).to_be_greater_than(0)
val composition = simple_web_layout_render_html_draw_ir(html, 320, 240)
expect(composition.batches.len()).to_be_greater_than(0)
val batch_commands = composition.batches[0].commands
expect(batch_commands.len()).to_be_greater_than(0)

val section = _command_for(batch_commands, "card_panel")
val heading = _command_for(batch_commands, "card_title")
val body = _command_for(batch_commands, "card_body")
expect(section).to_not_equal(nil)
expect(heading).to_not_equal(nil)
expect(body).to_not_equal(nil)

if section != nil:
    expect(section.width).to_be_greater_than(0)
    expect(section.height).to_be_greater_than(0)
if heading != nil:
    expect(heading.width).to_be_greater_than(0)
    expect(heading.height).to_be_greater_than(0)
if body != nil:
    expect(body.width).to_be_greater_than(0)
    expect(body.height).to_be_greater_than(0)
    if heading != nil:
        expect(heading.y).to_be_less_than(body.y)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_html_compat_core_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html compat core native

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
