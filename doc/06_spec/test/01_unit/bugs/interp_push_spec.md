# Interp Push Specification

> <details>

<!-- sdn-diagram:id=interp_push_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interp_push_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interp_push_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interp_push_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Push Specification

## Scenarios

### Module-level .push() bug

#### demonstrates workaround with concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_concat_workaround()).to_equal(3)
val items = _test_concat_items()
expect(_len(items)).to_equal(3)
expect(_get(items, 0)).to_equal("alpha")
expect(_get(items, 1)).to_equal("beta")
expect(_get(items, 2)).to_equal("gamma")
```

</details>

#### push works inside local scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_push_local()).to_equal(2)
expect(_test_push_local_first()).to_equal("one")
```

</details>

#### workaround preserves existing items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_preserve_items()).to_equal("second")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/interp_push_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module-level .push() bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
