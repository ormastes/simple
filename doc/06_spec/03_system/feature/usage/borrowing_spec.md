# borrowing_spec

> Reference Capabilities and Borrowing Specification

<!-- sdn-diagram:id=borrowing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=borrowing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

borrowing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=borrowing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# borrowing_spec

Reference Capabilities and Borrowing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Management |
| Status | In Progress |
| Source | `test/03_system/feature/usage/borrowing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Reference Capabilities and Borrowing Specification

Tests for the borrowing system including mutable (mut T), isolated (iso T),
and immutable reference capabilities. Verifies proper ownership transfer,
mutable access restrictions, and isolation guarantees.

## Scenarios

### Borrowing and Reference Capabilities

#### Immutable references

#### allows multiple immutable borrows

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### Mutable references

#### prevents simultaneous immutable and mutable borrows

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### Isolated references

#### ensures exclusive access to isolated values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### Ownership transfer

#### transfers ownership correctly through function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
