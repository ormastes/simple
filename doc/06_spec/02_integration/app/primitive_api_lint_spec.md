# Primitive Api Lint Specification

> 1. "pub fn truncate

<!-- sdn-diagram:id=primitive_api_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primitive_api_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primitive_api_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primitive_api_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive Api Lint Specification

## Scenarios

### primitive_api lint

#### flags bare primitive public function parameter and return types

1. "pub fn truncate
   - Expected: count_visible_primitive_api(source) equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn truncate(value: i64) -> i32:\n" +
    "    return value as i32\n"

expect(count_visible_primitive_api(source)).to_equal(2)
```

</details>

#### does not flag newunit semantic wrapper public APIs

1. "pub fn current user
   - Expected: count_visible_primitive_api(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "newunit UserId: i64 as uid\n" +
    "\n" +
    "pub fn current_user() -> UserId:\n" +
    "    return 42_uid\n"

expect(count_visible_primitive_api(source)).to_equal(0)
```

</details>

#### audits bool and text public primitives without changing lint count

1. "pub fn enabled

2. "    return name len
   - Expected: count_visible_primitive_api(source) equals `0`
   - Expected: entries.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn enabled(name: text) -> bool:\n" +
    "    return name.len() > 0\n"

val entries = primitive_api_audit_source(source, "sample.spl")
val report = primitive_api_audit_report(source, "sample.spl")
expect(count_visible_primitive_api(source)).to_equal(0)
expect(entries.len()).to_equal(2)
expect(report).to_contain("needs_domain_text_type")
expect(report).to_contain("needs_bool_wrapper_or_enum")
```

</details>

#### does not flag pure math signatures

1. "pub fn add
   - Expected: count_visible_primitive_api(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn add(left: i64, right: i64) -> i64:\n" +
    "    return left + right\n"

expect(count_visible_primitive_api(source)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/primitive_api_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- primitive_api lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
