# Language Port Specification

> 1. var session = SvimSession new

<!-- sdn-diagram:id=language_port_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=language_port_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

language_port_spec -> std
language_port_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=language_port_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Language Port Specification

## Scenarios

### svim language port

#### reads buffer text through the shared session

1. var session = SvimSession new
2. expect port buffer text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
val buffer_id = session.open_text("/tmp/demo.spl", "class Broken(\n")
val port = SvimLanguagePort.create_core()
expect port.buffer_text(session, buffer_id) to_equal "class Broken(\n"
```

</details>

#### publishes parser diagnostics into the quickfix list

1. var session = SvimSession new
2. session focus buffer
   - Expected: count > 0 is true
3. expect session quickfix items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
val buffer_id = session.open_text("/tmp/demo.spl", "value ]\n")
session.focus_buffer(buffer_id)
val port = SvimLanguagePort.create_core()
val count = port.publish_buffer_diagnostics(session, buffer_id)
expect(count > 0).to_equal(true)
expect session.quickfix.items.len() to_equal count
expect session.quickfix.items[0].severity to_equal "error"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svim/language_port_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svim language port

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
