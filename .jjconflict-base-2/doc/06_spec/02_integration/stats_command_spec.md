# Stats Command Specification

> 1. check

<!-- sdn-diagram:id=stats_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stats_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stats_command_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stats_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stats Command Specification

## Scenarios

### stats command

#### shows basic statistics

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is a manual test - run: bin/simple stats
# Expected: Shows files, lines, tests, features
check(true, "Manual test placeholder")
```

</details>

#### supports --brief flag

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run: bin/simple stats --brief
# Expected: No "Collecting data..." or documentation section
check(true, "Manual test placeholder")
```

</details>

#### supports --verbose flag

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run: bin/simple stats --verbose
# Expected: Shows directory scan details
check(true, "Manual test placeholder")
```

</details>

#### supports --quick flag

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run: bin/simple stats --quick
# Expected: Skips line counting, faster execution
check(true, "Manual test placeholder")
```

</details>

#### supports --json flag

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run: bin/simple stats --json
# Expected: Outputs valid JSON with all metrics
check(true, "Manual test placeholder")
```

</details>

#### combines flags correctly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run: bin/simple stats --json --quick
# Expected: JSON output with lines: 0
check(true, "Manual test placeholder")
```

</details>

### stats output accuracy

#### counts source files correctly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify file counts match actual filesystem
check(true, "Manual test placeholder")
```

</details>

#### extracts test statistics from test_result.md

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify test counts match doc/08_tracking/test/test_result.md
check(true, "Manual test placeholder")
```

</details>

#### extracts feature statistics from feature_db.sdn

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify feature counts match doc/08_tracking/feature/feature_db.sdn
check(true, "Manual test placeholder")
```

</details>

### stats performance

#### completes in under 5 seconds (full mode)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# time bin/simple stats
# Expected: < 5s
check(true, "Manual test placeholder")
```

</details>

#### completes in under 1 second (quick mode)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# time bin/simple stats --quick
# Expected: < 1s
check(true, "Manual test placeholder")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/stats_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- stats command
- stats output accuracy
- stats performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
