# Wine Advapi32 Service Specification

> <details>

<!-- sdn-diagram:id=wine_advapi32_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_advapi32_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_advapi32_service_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_advapi32_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Advapi32 Service Specification

## Scenarios

### Wine ADVAPI32 service-control bridge

#### executes a bounded service manager open-create-open-start-close sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_advapi32_execute_service_start(["OpenSCManagerW", "CreateServiceW", "OpenServiceW", "StartServiceW", "CloseServiceHandle"], "SimpleOSSCM", "WineEventLog")
expect(result.ok).to_equal(true)
expect(result.manager).to_equal("SimpleOSSCM")
expect(result.service).to_equal("WineEventLog")
expect(result.handle).to_be_greater_than(0)
expect(result.started).to_equal(true)
expect(result.operations).to_contain("OpenSCManagerW")
expect(result.operations).to_contain("StartServiceW")
expect(result.operations).to_contain("CloseServiceHandle")
```

</details>

#### keeps service-control dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_advapi32_execute_service_start(["CreateServiceW", "OpenSCManagerW", "OpenServiceW", "StartServiceW", "CloseServiceHandle"], "SCM", "Svc")
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("advapi32-service-sequence-expected:OpenSCManagerW")

val unsupported = wine_advapi32_execute_service_start(["OpenSCManagerW", "CreateServiceW", "OpenServiceW", "GetMessageW", "CloseServiceHandle"], "SCM", "Svc")
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("bridge-unsupported:GetMessageW")

val invalid = wine_advapi32_execute_service_start(["OpenSCManagerW", "CreateServiceW", "OpenServiceW", "StartServiceW", "CloseServiceHandle"], "SCM", "")
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("empty-service")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_advapi32_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine ADVAPI32 service-control bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
