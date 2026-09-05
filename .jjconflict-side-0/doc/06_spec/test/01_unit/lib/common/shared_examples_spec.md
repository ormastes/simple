# Shared Examples BDD Framework Specification

> shared_examples "name":

<!-- sdn-diagram:id=shared_examples_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_examples_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_examples_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_examples_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Examples BDD Framework Specification

shared_examples "name":

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEST-010, #TEST-011 |
| Category | Testing Framework |
| Status | Implemented |
| Source | `test/01_unit/lib/common/shared_examples_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
shared_examples "name":
it "test":
# test body

describe "context":
context "specific case":
it_behaves_like "name"
```

## Key Behaviors

- Shared examples are defined at describe block level
- Can be used in multiple test contexts
- Support fixture setup via given_lazy
- Variables bound in parent context are accessible in shared examples
- `include_examples` is an alias for `it_behaves_like`

## Scenarios

#### can test equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

#### can test boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### container has items

- expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = get_let(:container)
expect len(c) >= 0
```

</details>

#### value is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = get_let(:value)
expect v >= 0
```

</details>

### Shared Examples (TEST-010, TEST-011)

### Basic shared_examples usage

### Shared examples with fixtures

#### with a list container

#### with an empty container

#### with a numeric value

### Multiple shared examples in same context

#### with comprehensive setup

### Nested contexts with shared examples

#### outer context

#### inner context

### include_examples alias

#### using include_examples instead of it_behaves_like

### Shared Examples Edge Cases

### shared examples with no dependencies

#### can test constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

#### can test strings

- expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect len("hello") == 5
```

</details>

### shared examples in nested context

#### outer

#### works in nested context

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Shared examples with local state

#### first group

#### second group

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
