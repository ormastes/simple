# OCI Client Unit Tests

> Unit tests for the OCI (oras) client wrapper.

<!-- sdn-diagram:id=oci_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=oci_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

oci_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=oci_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OCI Client Unit Tests

Unit tests for the OCI (oras) client wrapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/package/oci_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the OCI (oras) client wrapper.

## Scenarios

### OCI Reference Format

#### constructs correct OCI ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = oci_ref("ghcr.io/simple-lang", "http", "1.0.0")
expect(ref).to_equal("ghcr.io/simple-lang/http:1.0.0")
```

</details>

#### handles scoped names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = oci_ref("ghcr.io/simple-lang", "my-lib", "0.1.0")
expect(ref).to_equal("ghcr.io/simple-lang/my-lib:0.1.0")
```

</details>

### Artifact Type

#### uses correct MIME type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = artifact_type()
expect(mime).to_equal("application/vnd.simple.package.v1+tar")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
