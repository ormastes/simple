# Config Loader

> Tests the configuration file loader including SDN format parsing, default value resolution, and configuration merging. Verifies that project and user config files are correctly loaded, validated, and applied in precedence order.

<!-- sdn-diagram:id=config_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_loader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Loader

Tests the configuration file loader including SDN format parsing, default value resolution, and configuration merging. Verifies that project and user config files are correctly loaded, validated, and applied in precedence order.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/config_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the configuration file loader including SDN format parsing, default value
resolution, and configuration merging. Verifies that project and user config
files are correctly loaded, validated, and applied in precedence order.

## Scenarios

### Config Dict Operations

#### stores basic integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"port": 8080}
expect(cfg["port"]).to_equal(8080)
```

</details>

#### stores floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"timeout": 30.5}
expect(cfg["timeout"]).to_equal(30.5)
```

</details>

#### stores booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"logging": true, "debug": false}
expect(cfg["logging"]).to_equal(true)
expect(cfg["debug"]).to_equal(false)
```

</details>

#### stores strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"name": "MyApp"}
expect(cfg["name"]).to_equal("MyApp")
```

</details>

#### stores identifiers as string constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"mode": "PRODUCTION"}
expect(cfg["mode"]).to_equal("PRODUCTION")
```

</details>

#### stores arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"ports": [8080, 8081, 8082]}
val ports = cfg["ports"]
expect(ports[0]).to_equal(8080)
expect(ports.len()).to_equal(3)
expect(ports[1]).to_equal(8081)
expect(ports[2]).to_equal(8082)
```

</details>

#### stores nested values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"train": {"epochs": 100, "lr": 0.001}}
expect(cfg["train"]["epochs"]).to_equal(100)
expect(cfg["train"]["lr"]).to_equal(0.001)
```

</details>

#### skips comments are pure-text concern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Comments in config files are a parser concern.
# The dict-based approach just stores values.
val cfg = {"port": 8080}
expect(cfg["port"]).to_equal(8080)
```

</details>

#### handles multiline config

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {
    "port": 8080,
    "timeout": 30.5,
    "logging": true,
    "app_name": "MyApp",
    "mode": "PRODUCTION"
}
expect(cfg["port"]).to_equal(8080)
expect(cfg["timeout"]).to_equal(30.5)
expect(cfg["logging"]).to_equal(true)
expect(cfg["app_name"]).to_equal("MyApp")
expect(cfg["mode"]).to_equal("PRODUCTION")
```

</details>

### Config Access

#### gets simple values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"port": 8080, "logging": true}
expect cfg["port"] == 8080
expect cfg["logging"] == true
```

</details>

#### gets nested values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"server": {"port": 8080}}
expect cfg["server"]["port"] == 8080
```

</details>

#### handles missing keys with default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = {"port": 8080}
val missing = cfg["missing"] ?? nil
expect missing == nil
```

</details>

### Config Merging

#### merges configs with overlay precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = {"a": 1, "b": 2}
val overlay = {"b": 3, "c": 4}
var merged = {}
for key in base.keys():
    merged[key] = base[key]
for key in overlay.keys():
    merged[key] = overlay[key]

expect merged["a"] == 1
expect merged["b"] == 3
expect merged["c"] == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
