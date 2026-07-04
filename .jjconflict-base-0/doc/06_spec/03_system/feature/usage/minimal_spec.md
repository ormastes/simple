# Minimal Test Spec

> A minimal smoke test that verifies the test runner can load a spec file with a basic describe/it block and execute a trivial assertion. Used as a baseline sanity check for the SPipe framework and test infrastructure.

<!-- sdn-diagram:id=minimal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=minimal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

minimal_spec -> db
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=minimal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Minimal Test Spec

A minimal smoke test that verifies the test runner can load a spec file with a basic describe/it block and execute a trivial assertion. Used as a baseline sanity check for the SPipe framework and test infrastructure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEST-002 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/03_system/feature/usage/minimal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A minimal smoke test that verifies the test runner can load a spec file
with a basic describe/it block and execute a trivial assertion. Used as a
baseline sanity check for the SPipe framework and test infrastructure.

## Syntax

```simple
describe "Test":
it "works":
check(true)
```

## Scenarios

### Test

#### works

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
