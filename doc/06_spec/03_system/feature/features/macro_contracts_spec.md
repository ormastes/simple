# macro_contracts_spec

> Macro contracts specification.

<!-- sdn-diagram:id=macro_contracts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_contracts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_contracts_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_contracts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_contracts_spec

Macro contracts specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_contracts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Macro contracts specification.

Tests the macro contract system including intro contracts for function
introduction, returns contracts for value emission, and inject contracts
for code injection at specific anchors.

## Scenarios

### Macro Contracts

### intro contracts

#### introduces functions to enclosing module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = contract_add_n(32)
expect(x).to_equal(42)
```

</details>

<details>
<summary>Advanced: introduces multiple functions from const-eval loop</summary>

#### introduces multiple functions from const-eval loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = contract_get_0() + contract_get_1() + contract_get_2()
expect(sum).to_equal(3)
```

</details>


</details>

### returns contracts

#### returns simple values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = contract_answer!()
expect(x).to_equal(42)
```

</details>

#### returns computed values from const-eval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = contract_compute!(8, 5)
expect(x).to_equal(42)
```

</details>

### inject contracts

#### injects code with tail anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = contract_test_fn()
expect(result).to_equal(42)
```

</details>

### combined contracts

#### uses intro and returns together

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val retrieved = contract_get_count()
expect(contract_initial).to_equal(100)
expect(retrieved).to_equal(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
