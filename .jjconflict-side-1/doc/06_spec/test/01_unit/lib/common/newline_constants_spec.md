# Newline Constants Specification

> <details>

<!-- sdn-diagram:id=newline_constants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=newline_constants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

newline_constants_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=newline_constants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Newline Constants Specification

## Scenarios

### Newline Constants

#### keeps newline translation modes available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = platform_newline_source()

expect(source).to_contain("enum TextMode:")
expect(source).to_contain("Binary")
expect(source).to_contain("Text")
expect(source).to_contain("Remote")
```

</details>

#### keeps host and remote read/write translation paths available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = platform_newline_source()

expect(source).to_contain("fn translate_write(content: text, mode: TextMode, remote: PlatformConfig) -> text")
expect(source).to_contain("fn translate_read(content: text, mode: TextMode, remote: PlatformConfig) -> text")
expect(source).to_contain("send_text(host, host, content)")
expect(source).to_contain("recv_text(host, remote, content)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/newline_constants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Newline Constants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
