# Md Wiki Index Specification

> <details>

<!-- sdn-diagram:id=md_wiki_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_wiki_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_wiki_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_wiki_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Wiki Index Specification

## Scenarios

### markdown wiki daily notes

#### normalizes daily-note extension, path, and template content in the shared service

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = md_wiki_daily_note_config_with_title("Daily/", "Log {{date}}", "markdown", "# {{title}}\n{{date}}\n")
expect(config.extension).to_equal(".markdown")
expect(md_wiki_daily_note_path(config, "2026-05-30")).to_equal("Daily/Log 2026-05-30.markdown")
expect(md_wiki_daily_note_content(config, "2026-05-30")).to_equal("# Log 2026-05-30\n2026-05-30\n")
```

</details>

#### keeps app daily-note commands on shared wiki services

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = read_text("src/app/editor/editor_ctrl_wiki.spl")
val monolith = read_text("src/app/editor/editor_controller.spl")
val helpers = read_text("src/app/editor/editor_path_text_helpers.spl")
expect(ctrl.contains("md_wiki_daily_note_config_with_title")).to_equal(true)
expect(ctrl.contains("md_wiki_daily_note_path")).to_equal(true)
expect(ctrl.contains("md_wiki_daily_note_content")).to_equal(true)
expect(monolith.contains("md_wiki_daily_note_config_with_title")).to_equal(true)
expect(helpers.contains("fn _editor_daily_note_extension(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/md_wiki_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown wiki daily notes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
