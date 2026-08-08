# Package Cli Specification

> <details>

<!-- sdn-diagram:id=package_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=package_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

package_cli_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=package_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Cli Specification

## Scenarios

### Package Cli

#### keeps package commands visible in CLI help

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = cli_help_source()

expect(source).to_contain("Package Management:")
expect(source).to_contain("simple add <pkg> [options]")
expect(source).to_contain("simple remove <pkg>")
expect(source).to_contain("simple install")
expect(source).to_contain("simple update [pkg]")
expect(source).to_contain("simple list")
expect(source).to_contain("simple tree")
```

</details>

#### keeps package registry data model available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_registry_source("types.spl")

expect(source).to_contain("class RegistryConfig:")
expect(source).to_contain("class PackageInfo:")
expect(source).to_contain("class VersionEntry:")
expect(source).to_contain("class VersionDependency:")
expect(source).to_contain("class PublishResult:")
```

</details>

#### keeps package registry trust and signing surfaces available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trust = package_registry_source("trust.spl")
val signing = package_registry_source("signing.spl")

expect(trust).to_contain("enum TrustLevel:")
expect(trust).to_contain("class TrustedSigner:")
expect(trust).to_contain("class TrustStore:")
expect(signing).to_contain("class PackageSignature:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package Cli

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
