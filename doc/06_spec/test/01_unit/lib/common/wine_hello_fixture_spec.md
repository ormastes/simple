# Wine Hello Fixture Specification

> <details>

<!-- sdn-diagram:id=wine_hello_fixture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_hello_fixture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_hello_fixture_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_hello_fixture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Fixture Specification

## Scenarios

### Wine hello fixture

#### builds the known executable milestone fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.stdout_handle).to_equal(-11)
expect(result.bytes_written).to_equal(25)
expect(result.exit_code).to_equal(0)
expect(wine_hello_exe_can_execute(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_hello_fixture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine hello fixture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
