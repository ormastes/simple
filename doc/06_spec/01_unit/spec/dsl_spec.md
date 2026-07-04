# Dsl Specification

> <details>

<!-- sdn-diagram:id=dsl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dsl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dsl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dsl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dsl Specification

## Scenarios

### BDD DSL

#### describe

#### registers a top-level example group

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    nil

val groups = get_all_groups()
expect(groups.len()).to_equal(1)
expect(groups[0].description).to_equal("Calculator")
```

</details>

#### can contain nested contexts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    context "addition":
        nil

val groups = get_all_groups()
val calc_group = groups[0]
expect(calc_group.children.len()).to_equal(1)
expect(calc_group.children[0].description).to_equal("addition")
```

</details>

#### can contain multiple nested contexts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    context "addition":
        nil
    context "subtraction":
        nil

val groups = get_all_groups()
expect(groups[0].children.len()).to_equal(2)
```

</details>

#### context

#### creates nested example groups within describe

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    context "when adding":
        nil

val groups = get_all_groups()
expect(groups[0].children.len()).to_equal(1)
expect(groups[0].children[0].description).to_equal("when adding")
```

</details>

#### can be nested multiple levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    context "addition":
        context "with positive numbers":
            nil

val groups = get_all_groups()
val calc = groups[0]
val addition = calc.children[0]
expect(addition.children.len()).to_equal(1)
expect(addition.children[0].description).to_equal("with positive numbers")
```

</details>

#### creates top-level group if called outside describe

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
context "standalone context":
    nil

val groups = get_all_groups()
expect(groups.len()).to_equal(1)
expect(groups[0].description).to_equal("standalone context")
```

</details>

#### it

#### registers an example within a group

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    it "adds numbers":
        nil

val groups = get_all_groups()
expect(groups[0].test_examples.len()).to_equal(1)
expect(groups[0].test_examples[0].description).to_equal("adds numbers")
```

</details>

#### can register multiple examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    it "adds numbers":
        nil
    it "subtracts numbers":
        nil

val groups = get_all_groups()
expect(groups[0].test_examples.len()).to_equal(2)
```

</details>

#### executes the example block when run

1. groups[0] test examples[0] run
   - Expected: executed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
describe "Test":
    it "runs the block":
        executed = true

val groups = get_all_groups()
groups[0].test_examples[0].run()
expect(executed).to_equal(true)
```

</details>

#### skip

#### registers a skipped example

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    dsl.skip "not yet implemented":
        nil

val groups = get_all_groups()
val example = groups[0].test_examples[0]
expect(example.is_skipped).to_equal(true)
expect(example.is_pending()).to_equal(true)
```

</details>

#### ignore_it

### Test

### Test

#### Hooks - before_each

#### registers a BeforeEach hook

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    before_each:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_before_each_hooks()
expect(hooks.len()).to_equal(1)
```

</details>

#### can register multiple before_each hooks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    before_each:
        nil
    before_each:
        nil

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(2)
```

</details>

#### Hooks - after_each

#### registers an AfterEach hook

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    after_each:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_after_each_hooks()
expect(hooks.len()).to_equal(1)
```

</details>

#### Hooks - before_all

#### registers a BeforeAll hook

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    before_all:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_before_all_hooks()
expect(hooks.len()).to_equal(1)
```

</details>

#### Hooks - after_all

#### registers an AfterAll hook

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    after_all:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_after_all_hooks()
expect(hooks.len()).to_equal(1)
```

</details>

#### let_lazy

#### registers a lazy memoized value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    let_lazy :value, \: 42

val groups = get_all_groups()
# let_lazy creates a before_each hook that sets up memoization
val hooks = groups[0].get_before_each_hooks()
expect(hooks.len()).to_equal(1)
```

</details>

#### can register multiple lazy values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    let_lazy :value1, \: 42
    let_lazy :value2, \: "hello"

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(2)
```

</details>

#### given

#### registers an eager setup block as before_each

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    given:
        nil

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(1)
```

</details>

#### can register multiple given blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    given:
        nil
    given:
        nil

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(2)
```

</details>

#### given_lazy

#### registers a lazy fixture in context definition

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
context_def :test_context:
    given_lazy :data, \: "test data"

match get_context(:test_context):
    case Some(ctx_def):
        expect(ctx_def.givens.len()).to_equal(1)
    case None:
        fail("Expected context definition to be registered")
```

</details>

#### registers a before_each hook in regular context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Test":
    given_lazy :user, \: "admin"

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(1)
```

</details>

#### context_def

#### registers a reusable context definition

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
context_def :admin_user:
    given_lazy :user, \: "admin"

match get_context(:admin_user):
    case Some(ctx_def):
        expect(ctx_def.name.to_string()).to_equal("admin_user")
    case None:
        fail("Expected context to be registered")
```

</details>

#### can contain multiple givens

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
context_def :test_context:
    given:
        nil
    given_lazy :data, \: "test"

match get_context(:test_context):
    case Some(ctx_def):
        expect(ctx_def.givens.len()).to_equal(2)
    case None:
        fail("Expected context to be registered")
```

</details>

#### shared_examples

#### registers a shared example definition

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_examples "stack-like":
    it "supports push":
        nil

match get_shared_examples("stack-like"):
    case Some(shared_def):
        expect(shared_def.name).to_equal("stack-like")
    case None:
        fail("Expected shared example to be registered")
```

</details>

#### can have a description

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_examples "stack-like", "Container with stack operations":
    nil

match get_shared_examples("stack-like"):
    case Some(shared_def):
        match shared_def.description:
            case Some(desc):
                expect(desc).to_equal("Container with stack operations")
            case None:
                fail("Expected description to be set")
    case None:
        fail("Expected shared example to be registered")
```

</details>

#### it_behaves_like

#### includes shared examples in current context

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_examples "collection-like":
    it "has size":
        nil

describe "Array":
    it_behaves_like "collection-like"

val groups = get_all_groups()
val array_group = groups[0]
# it_behaves_like creates a nested context
expect(array_group.children.len()).to_equal(1)
expect(array_group.children[0].description).to_equal("behaves like collection-like")
```

</details>

#### shared examples have access to parent context

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_examples "addable":
    it "adds numbers":
        # In real usage, this would access parent context helpers
        nil

describe "Calculator":
    it_behaves_like "addable"

val groups = get_all_groups()
val calc_group = groups[0]
val behaves_context = calc_group.children[0]
expect(behaves_context.test_examples.len()).to_equal(1)
```

</details>

#### include_examples

#### is an alias for it_behaves_like

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_examples "enumerable":
    it "supports each":
        nil

describe "Array":
    include_examples "enumerable"

val groups = get_all_groups()
expect(groups[0].children.len()).to_equal(1)
expect(groups[0].children[0].description).to_equal("behaves like enumerable")
```

</details>

#### Full integration

#### supports complex nested structure with hooks and examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
describe "Calculator":
    before_all:
        nil
    before_each:
        nil

    context "addition":
        before_each:
            nil

        it "adds positive numbers":
            nil

        it "adds negative numbers":
            nil

    context "subtraction":
        it "subtracts numbers":
            nil

    after_each:
        nil
    after_all:
        nil

val groups = get_all_groups()
val calc = groups[0]

# Check top-level hooks
expect(calc.get_before_all_hooks().len()).to_equal(1)
expect(calc.get_before_each_hooks().len()).to_equal(1)
expect(calc.get_after_each_hooks().len()).to_equal(1)
expect(calc.get_after_all_hooks().len()).to_equal(1)

# Check nested contexts
expect(calc.children.len()).to_equal(2)

# Check addition context
val addition = calc.children[0]
expect(addition.description).to_equal("addition")
expect(addition.test_examples.len()).to_equal(2)
expect(addition.get_before_each_hooks().len()).to_equal(1)

# Check subtraction context
val subtraction = calc.children[1]
expect(subtraction.description).to_equal("subtraction")
expect(subtraction.test_examples.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/dsl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BDD DSL
- Calculator
- Calculator
- Calculator
- Calculator
- Calculator
- Calculator
- Calculator
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Test
- Array
- Calculator
- Array
- Calculator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
