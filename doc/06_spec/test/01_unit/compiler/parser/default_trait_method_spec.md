# Default trait methods spec

> _Executable checks for default trait method behavior._

<!-- sdn-diagram:id=default_trait_method_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=default_trait_method_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

default_trait_method_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=default_trait_method_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default trait methods spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/default_trait_method_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### default trait methods
_Executable checks for default trait method behavior._

#### trait with only defaults parses and resolves

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Greetable has only default methods -- no required ones
val result = greet_formal_default()
expect(result).to_equal("Good day, sir.")
```

</details>

#### default methods are inherited when not overridden

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = greet_casual_default()
expect(result).to_equal("Hey!")
```

</details>

#### required method can be implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = formal_person_to_string()
expect(result).to_equal("FormalPerson(Alice)")
```

</details>

#### default method can be overridden in impl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = casual_greet()
expect(result).to_equal("Yo, what's up!")
```

</details>

### trait definition structure
_Structural checks that avoid placeholder assertions._

#### trait with mixed required and default methods parses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(printable_default_method_count()).to_equal(2)
expect(formal_person_to_string()).to_contain("Alice")
```

</details>

#### all-default trait behavior is available without dummy impl bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(greetable_required_method_count()).to_equal(0)
expect(greet_formal_default()).to_equal("Good day, sir.")
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
