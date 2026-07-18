# Itf Config Specification

> <details>

<!-- sdn-diagram:id=itf_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=itf_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

itf_config_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=itf_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Itf Config Specification

## Scenarios

### ITF configuration

#### ItfConfig.default

#### creates config with sensible defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ItfConfig.default()
expect(config.confluence_url).to_equal("")
expect(config.jira_acli_path).to_equal("acli")
expect(config.default_output).to_equal("text")
expect(config.color_mode).to_equal("auto")
```

</details>

#### ItfError

#### auth error has exit code 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ItfError.auth("missing token")
expect(err.exit_code()).to_equal(4)
```

</details>

#### cancelled error has exit code 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ItfError.cancelled()
expect(err.exit_code()).to_equal(2)
```

</details>

#### api error has exit code 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ItfError.api(500, "internal error")
expect(err.exit_code()).to_equal(1)
```

</details>

#### not found has exit code 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ItfError.not_found("page 123")
expect(err.exit_code()).to_equal(1)
```

</details>

#### conflict error has exit code 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ItfError.conflict(5, 6)
expect(err.exit_code()).to_equal(1)
```

</details>

#### displays trace id when present

1. var err = ItfError api
2. err = ItfError


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var err = ItfError.api(500, "server error")
err = ItfError(kind: err.kind, message: err.message, status_code: err.status_code, trace_id: "ABC123")
val display = err.display()
expect(display).to_contain("trace: ABC123")
```

</details>

#### omits trace id when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ItfError.api(500, "server error")
val display = err.display()
expect(display).to_contain("error: server error")
```

</details>

#### resolve_editor

#### returns vi as default when no overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ItfConfig.default()
val editor = resolve_editor(config)
# Will return vi or whatever EDITOR env var is set
expect(editor.len()).to_be_greater_than(0)
```

</details>

#### uses config override when set

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ItfConfig(
    confluence_url: "",
    confluence_user: "",
    confluence_default_space: "",
    jira_url: "",
    jira_acli_path: "acli",
    default_output: "text",
    color_mode: "auto",
    editor_override: "nano",
    pager_override: ""
)
val editor = resolve_editor(config)
expect(editor).to_equal("nano")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/itf_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ITF configuration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
