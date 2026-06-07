# Grammar Test Specification

> 1. check

<!-- sdn-diagram:id=grammar_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=grammar_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

grammar_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=grammar_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grammar Test Specification

## Scenarios

### GrammarTestCase

#### creates test case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test = MockTestCase.new("test_grammar")
check(test.name == "test_grammar")
```

</details>

#### runs test case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test = MockTestCase.new("test")
check(test.run())
```

</details>

#### reports test results

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test = MockTestCase.new("test")
val result = test.report_results()
check(result == "PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/grammar_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GrammarTestCase

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
