# Sfm Specification

> <details>

<!-- sdn-diagram:id=sfm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sfm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sfm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sfm Specification

## Scenarios

### SFM manifest — payment module packaging

### manifest structure

#### has Trusted security level

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
expect manifest.security_level == SfmSecurityLevel.Trusted
```

</details>

#### has correct module name

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
expect manifest.manifest_name == "simple-payment"
```

</details>

#### has version 0.1.0

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
expect manifest.version == "0.1.0"
```

</details>

### layers

#### exposes 4 layers (gateway, vault, cli, agent)

1. expect manifest layers length


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
expect manifest.layers.length() == 4
```

</details>

#### gateway layer is privileged back-service

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
val gw = manifest.layers[0]
expect gw.role == "gateway"
expect gw.kind == LayerKind.BackService
expect gw.privileged == true
```

</details>

#### vault layer is privileged back-service

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
val v = manifest.layers[1]
expect v.role == "vault"
expect v.kind == LayerKind.BackService
expect v.privileged == true
```

</details>

#### cli layer is non-privileged front-cli

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
val cli = manifest.layers[2]
expect cli.role == "cli"
expect cli.kind == LayerKind.FrontCli
expect cli.privileged == false
```

</details>

#### agent layer is non-privileged front-agent

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
val ag = manifest.layers[3]
expect ag.role == "agent"
expect ag.kind == LayerKind.FrontAgent
expect ag.privileged == false
```

</details>

### authz gate

#### privileged layers require Trusted security level

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = payment_sfm_manifest()
expect manifest.security_level == SfmSecurityLevel.Trusted
var priv_count = 0
var i = 0
while i < manifest.layers.length():
    if manifest.layers[i].privileged:
        priv_count = priv_count + 1
    i = i + 1
expect priv_count == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/sfm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SFM manifest — payment module packaging
- manifest structure
- layers
- authz gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
