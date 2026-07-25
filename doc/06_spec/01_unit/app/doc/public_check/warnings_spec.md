# Warnings Specification

> <details>

<!-- sdn-diagram:id=warnings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=warnings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

warnings_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=warnings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Warnings Specification

## Scenarios

### Warnings

#### keeps public documentation warning model available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/doc/public_check/warnings.spl") ?? ""

expect(source).to_contain("struct PublicWarning")
expect(source).to_contain("static fn new(")
expect(source).to_contain("fn check_public_comments(module_path: text) -> [PublicWarning]")
```

</details>

#### keeps public documentation warning formatting available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/doc/public_check/warnings.spl") ?? ""

expect(source).to_contain("fn format_warning(warning: PublicWarning) -> text")
expect(source).to_contain("fn emit_warnings(warnings: [PublicWarning])")
expect(source).to_contain("fn warnings_to_json(warnings: [PublicWarning]) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc/public_check/warnings_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Warnings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
