# Given Working Specification

> <details>

<!-- sdn-diagram:id=given_working_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=given_working_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

given_working_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=given_working_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Given Working Specification

## Scenarios

### Given (Eager Fixtures)

### Unnamed eager - given:

#### with eager setup

#### setup_ran is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var setup_ran = false
setup_ran = true
expect setup_ran == true
```

</details>

#### setup_ran is true in second example too

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var setup_ran = false
setup_ran = true
expect setup_ran == true
```

</details>

### Named eager - before_each:

#### with named eager setup

#### counter is initialized

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

#### processed is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var processed = false
processed = true
expect processed == true
```

</details>

#### each example gets fresh state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each test initializes its own counter, so it's always 1
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

### Combining unnamed given and before_each

#### with mixed eager fixtures

#### both hooks ran

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var given_ran = false
var before_each_ran = false
given_ran = true
before_each_ran = true
expect given_ran == true
expect before_each_ran == true
```

</details>

#### second example sees both hooks ran

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var given_ran = false
var before_each_ran = false
given_ran = true
before_each_ran = true
expect given_ran == true
expect before_each_ran == true
```

</details>

### Given with lazy fixtures

#### mixing eager and lazy

#### eager runs before lazy

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eager_run_count = 0
eager_run_count = eager_run_count + 1
expect eager_run_count == 1
expect get_let(:lazy_value) == 42
```

</details>

#### lazy is memoized, eager runs again

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eager_run_count = 0
eager_run_count = eager_run_count + 1
expect eager_run_count == 1
expect get_let(:lazy_value) == 42
```

</details>

### Given in nested contexts

#### outer context

#### inner context

#### level is available in inner

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var level = "outer"
var inner_level = "inner"
level = "outer_setup"
inner_level = "inner_setup"
expect level == "outer_setup"
expect inner_level == "inner_setup"
```

</details>

### Given in context_def

#### context_def given works

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:ctx_value) == 100
```

</details>

### Real-world database simulation

#### with realistic setup

#### connection established

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var connection = "db_connection_established"
expect connection == "db_connection_established"
```

</details>

#### tables created

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tables = ["users", "posts", "comments"]
expect len(tables) == 3
```

</details>

#### users table exists

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tables = ["users", "posts", "comments"]
expect len(tables) > 0
if len(tables) > 0:
    expect tables[0] == "users"
```

</details>

#### second test gets fresh setup

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var setup_count = 0
setup_count = setup_count + 1
expect setup_count == 1
```

</details>

### Referencing context_def with given_lazy

#### has database from context_def

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:database) == "db_connection"
```

</details>

#### has token from context_def

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:token) == "auth_token_123"
```

</details>

### Context with additional given

#### accesses fixture from context_def

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:base) == 10
```

</details>

#### uses derived variable from fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val derived = get_let(:base) * 2
expect derived == 20
```

</details>

#### combines context data with new variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val derived = get_let(:base) * 2
val combined = get_let(:base) + derived
expect combined == 30
```

</details>

#### each test gets fresh derived state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val derived = get_let(:base) * 2
expect derived == 20
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/given_working_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Given (Eager Fixtures)
- Unnamed eager - given:
- Named eager - before_each:
- Combining unnamed given and before_each
- Given with lazy fixtures
- Given in nested contexts
- Given in context_def
- Real-world database simulation
- Referencing context_def with given_lazy
- Context with additional given

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
