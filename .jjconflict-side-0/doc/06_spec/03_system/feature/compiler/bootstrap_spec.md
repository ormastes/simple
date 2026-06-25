# Direct Bootstrap System

> Tests the direct bootstrap system including stage transitions from Rust seed to self-hosted Simple compiler. Verifies that each bootstrap stage produces a functional compiler capable of compiling the next stage.

<!-- sdn-diagram:id=bootstrap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# Direct Bootstrap System

Tests the direct bootstrap system including stage transitions from Rust seed to self-hosted Simple compiler. Verifies that each bootstrap stage produces a functional compiler capable of compiling the next stage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/bootstrap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the direct bootstrap system including stage transitions from Rust seed to
self-hosted Simple compiler. Verifies that each bootstrap stage produces a
functional compiler capable of compiling the next stage.


</details>
