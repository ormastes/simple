# Registry Publish

> Tests the package registry publish workflow including package validation, version bumping, and upload to the Simple package registry. Verifies that metadata, checksums, and dependency declarations are correctly assembled.

<!-- sdn-diagram:id=publish_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=publish_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

publish_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=publish_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Registry Publish

Tests the package registry publish workflow including package validation, version bumping, and upload to the Simple package registry. Verifies that metadata, checksums, and dependency declarations are correctly assembled.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/publish_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the package registry publish workflow including package validation,
version bumping, and upload to the Simple package registry. Verifies that
metadata, checksums, and dependency declarations are correctly assembled.

## Scenarios

### Publish Command

#### when manifest is valid

#### parses package name from manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "package:\n  name: my-pkg\n  version: 1.0.0\n"
val info = parse_manifest(content)
expect(info[0]).to_equal("my-pkg")
```

</details>

#### parses package version from manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "package:\n  name: my-pkg\n  version: 2.1.0\n"
val info = parse_manifest(content)
expect(info[1]).to_equal("2.1.0")
```

</details>

#### when manifest is missing

#### returns error when no simple.sdn exists

1. setup publish empty dir
   - Expected: code equals `1`
   - Expected: (out + err) does not contain `Publishing `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_publish_empty_dir()
val (out, err, code) = run_publish(["--dry-run"])
expect(code).to_equal(1)
expect((out + err).contains("Publishing ")).to_equal(false)
```

</details>

#### when using --dry-run

#### does not push to GHCR in dry-run mode

1. setup publish fixture
   - Expected: code equals `0`
   - Expected: out does not contain `Pushing to GHCR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_publish_fixture("package:\n  name: dry-pkg\n  version: 3.4.5")
val (out, err, code) = run_publish(["--dry-run"])
expect(code).to_equal(0)
expect(out).to_contain("Publishing dry-pkg@3.4.5")
expect(out).to_contain("(dry run - no changes made)")
expect(out.contains("Pushing to GHCR")).to_equal(false)
```

</details>

### SPK Tarball

#### when building tarball

#### excludes .jj directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_include_in_spk(".jj/store/op_heads")).to_equal(false)
```

</details>

#### excludes target directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_include_in_spk("target/pkg/app.spk")).to_equal(false)
```

</details>

#### excludes .env files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_include_in_spk("local.env")).to_equal(false)
```

</details>

#### includes simple.sdn manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_include_in_spk("simple.sdn")).to_equal(true)
```

</details>

#### includes src directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_include_in_spk("src/main.spl")).to_equal(true)
```

</details>

### Checksum

#### computes sha256 checksum with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Checksum format: sha256:<hex>
expect(valid_sha256_checksum("sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")).to_equal(true)
expect(valid_sha256_checksum("0123456789abcdef")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
