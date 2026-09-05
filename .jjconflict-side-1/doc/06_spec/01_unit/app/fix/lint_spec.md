# Lint Specification

> <details>

<!-- sdn-diagram:id=lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Specification

## Scenarios

### Spec file lint rules

#### print_in_test_spec

#### detects print in spec files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "it \"test\":\n    print(42)\n"
val fixes = check_print_in_test_spec(source, "my_spec.spl")
expect(fixes.len()).to_equal(1)
```

</details>

#### ignores non-spec files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    print(42)\n"
val fixes = check_print_in_test_spec(source, "main.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### spipe_missing_docstrings

#### detects missing docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    it \"y\":\n        expect true\n"
val fixes = check_spipe_missing_docstrings(source, "test_spec.spl")
expect(fixes.len() >= 1).to_equal(true)
```

</details>

#### spipe_manual_assertions

#### detects manual assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if x > 5: fail(\"too big\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
expect(fixes.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/fix/lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Spec file lint rules

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
