# Spec Coverage Log Modes Specification

> 1.  setup empty fixture

<!-- sdn-diagram:id=spec_coverage_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spec_coverage_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spec_coverage_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spec_coverage_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Coverage Log Modes Specification

## Scenarios

### spec-coverage log mode CLI options

#### shows shared log options in help

1.  setup empty fixture
   - Expected: code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_empty_fixture()
val (out, err, code) = _run_spec_coverage(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for missing feature database

1.  setup empty fixture
   - Expected: code equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_empty_fixture()
val (out, err, code) = _run_spec_coverage(["--log-mode=json"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"spec-coverage\"")
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("\"total\":0")
```

</details>

#### supports dot progress

1.  setup feature fixture
   - Expected: code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_feature_fixture()
val (out, err, code) = _run_spec_coverage(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_contain(".")
expect(out).to_contain("Total features: 2")
```

</details>

#### rejects invalid log mode

1.  setup empty fixture
   - Expected: code equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_empty_fixture()
val (out, err, code) = _run_spec_coverage(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spec_coverage_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spec-coverage log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
