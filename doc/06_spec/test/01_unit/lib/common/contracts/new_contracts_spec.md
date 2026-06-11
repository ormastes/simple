# New Contracts Specification

> 1. simple contract check

<!-- sdn-diagram:id=new_contracts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=new_contracts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

new_contracts_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=new_contracts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# New Contracts Specification

## Scenarios

### std.contracts.contracts

#### simple_contract_check (passing condition)

#### returns silently when condition is 1

1. simple contract check
   - Expected: "test_fn" equals `test_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check(1, 0, "test_fn")
expect("test_fn").to_equal("test_fn")
```

</details>

#### returns silently when condition is non-zero

1. simple contract check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check(100, 1, "another_fn")
expect(100).to_be_greater_than(1)
```

</details>

#### accepts kind=2 (error postcondition)

1. simple contract check
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check(1, 2, "err_post_fn")
expect(2).to_equal(2)
```

</details>

#### accepts empty function name

1. simple contract check
   - Expected: "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check(1, 0, "")
expect("").to_equal("")
```

</details>

#### accepts kind=5 (assertion)

1. simple contract check
   - Expected: 5 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check(1, 5, "assert_fn")
expect(5).to_equal(5)
```

</details>

#### simple_contract_check_msg (passing condition)

#### returns silently when condition is 1

1. simple contract check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check_msg(1, 0, "fn_name", "all good")
expect("all good").to_contain("good")
```

</details>

#### accepts empty message

1. simple contract check msg
   - Expected: "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check_msg(1, 1, "fn_name", "")
expect("").to_equal("")
```

</details>

#### accepts empty function name and message

1. simple contract check msg
   - Expected: 3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simple_contract_check_msg(1, 3, "", "")
expect(3).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/new_contracts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.contracts.contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
