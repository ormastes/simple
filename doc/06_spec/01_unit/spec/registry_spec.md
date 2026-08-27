# registry_spec

> Unit tests for the BDD Registry module.

<!-- sdn-diagram:id=registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

registry_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# registry_spec

Unit tests for the BDD Registry module.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the BDD Registry module.

This test file verifies the core components of the BDD test registry system:
- Example: Test case representation with skip, slow, timeout, and tag support
- ExampleGroup: Hierarchical grouping of test cases with hooks
- Registry functions: Global registration and retrieval of test groups

Uses mock implementations to isolate registry logic from the actual test framework.

## Scenarios

### BDD Registry

#### Example

#### creates a new example with description and block

1. expect example tags len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test description", \: ())
expect example.description == "test description"
expect example.is_skipped == false
expect example.tags.len() == 0
```

</details>

#### can be marked as skipped

1. expect example is pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).skip()
expect example.is_skipped == true
expect example.is_pending() == true
```

</details>

#### can be marked as slow

1. expect example has tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).slow()
expect example.has_tag("slow") == true
```

</details>

#### can have a timeout set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).with_timeout(30)
match example.timeout_seconds:
    case Some(timeout): expect timeout == 30
    case nil: expect false
```

</details>

#### can have tags added

1. expect example has tag
2. expect example has tag
3. expect example has tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).with_tag("integration").with_tag("database")
expect example.has_tag("integration") == true
expect example.has_tag("database") == true
expect example.has_tag("nonexistent") == false
```

</details>

#### should_run returns false for skipped examples

1. expect example should run


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).skip()
expect example.should_run(true) == false
```

</details>

#### should_run returns false for slow examples when run_slow is false

1. expect example should run


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).slow()
expect example.should_run(false) == false
```

</details>

#### should_run returns true for slow examples when run_slow is true

1. expect example should run


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = Example.create("test", \: ()).slow()
expect example.should_run(true) == true
```

</details>

#### ExampleGroup

#### creates a new group with description

1. expect group children len
2. expect group test examples len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = ExampleGroup.create("MyClass", nil)
expect group.description == "MyClass"
expect group.children.len() == 0
expect group.test_examples.len() == 0
```

</details>

#### can add examples

1. group add example
2. expect group test examples len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = ExampleGroup.create("Test", nil)
val example = Example.create("does something", \: ())
group.add_example(example)
expect group.test_examples.len() == 1
expect group.test_examples[0].description == "does something"
```

</details>

#### full_description returns description for top-level group

1. expect group full description


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = ExampleGroup.create("Calculator", nil)
expect group.full_description() == "Calculator"
```

</details>

#### example_count returns count of direct examples

1. group add example
2. group add example
3. expect group example count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = ExampleGroup.create("Test", nil)
group.add_example(Example.create("test 1", \: ()))
group.add_example(Example.create("test 2", \: ()))
expect group.example_count() == 2
```

</details>

#### Registry - Groups

#### can register example groups

1. reset registry
2. register group
3. expect groups len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_registry()
val group = ExampleGroup.create("Test", nil)
register_group(group)
val groups = get_all_groups()
expect groups.len() == 1
expect groups[0].description == "Test"
```

</details>

#### can clear all groups

1. reset registry
2. register group
3. clear groups
4. expect get all groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_registry()
register_group(ExampleGroup.create("Test", nil))
clear_groups()
expect get_all_groups().len() == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
