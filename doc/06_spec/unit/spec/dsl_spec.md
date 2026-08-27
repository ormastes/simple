# dsl_spec

> Purpose: registers a top-level example group

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dsl_spec

Purpose: registers a top-level example group

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/spec/dsl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: registers a top-level example group
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### BDD DSL

#### describe

#### registers a top-level example group

- registers a top-level example group
- Verify: registers a top-level example group
   - Expected: groups.len() equals `1`
   - Expected: groups[0].description equals `Calculator`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a top-level example group")
step("Verify: registers a top-level example group")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    nil

val groups = get_all_groups()
expect(groups.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(groups[0].description).to_equal("Calculator")
```

</details>

#### can contain nested contexts

- can contain nested contexts
- Verify: can contain nested contexts
   - Expected: calc_group.children.len() equals `1`
   - Expected: calc_group.children[0].description equals `addition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can contain nested contexts")
step("Verify: can contain nested contexts")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    context "addition":
        nil

val groups = get_all_groups()
val calc_group = groups[0]
expect(calc_group.children.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(calc_group.children[0].description).to_equal("addition")
```

</details>

#### can contain multiple nested contexts

- can contain multiple nested contexts
- Verify: can contain multiple nested contexts
   - Expected: groups[0].children.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can contain multiple nested contexts")
step("Verify: can contain multiple nested contexts")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    context "addition":
        nil
    context "subtraction":
        nil

val groups = get_all_groups()
expect(groups[0].children.len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### context

#### creates nested example groups within describe

- creates nested example groups within describe
- Verify: creates nested example groups within describe
   - Expected: groups[0].children.len() equals `1`
   - Expected: groups[0].children[0].description equals `when adding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates nested example groups within describe")
step("Verify: creates nested example groups within describe")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    context "when adding":
        nil

val groups = get_all_groups()
expect(groups[0].children.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(groups[0].children[0].description).to_equal("when adding")
```

</details>

#### can be nested multiple levels

- can be nested multiple levels
- Verify: can be nested multiple levels
   - Expected: addition.children.len() equals `1`
   - Expected: addition.children[0].description equals `with positive numbers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be nested multiple levels")
step("Verify: can be nested multiple levels")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    context "addition":
        context "with positive numbers":
            nil

val groups = get_all_groups()
val calc = groups[0]
val addition = calc.children[0]
expect(addition.children.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(addition.children[0].description).to_equal("with positive numbers")
```

</details>

#### creates top-level group if called outside describe

- creates top-level group if called outside describe
- Verify: creates top-level group if called outside describe
   - Expected: groups.len() equals `1`
   - Expected: groups[0].description equals `standalone context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates top-level group if called outside describe")
step("Verify: creates top-level group if called outside describe")
# @req: REQ-SPEC-Dsl-001
context "standalone context":
    nil

val groups = get_all_groups()
expect(groups.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(groups[0].description).to_equal("standalone context")
```

</details>

#### it

#### registers an example within a group

- registers an example within a group
- Verify: registers an example within a group
- adds numbers
- Verify: adds numbers
   - Expected: groups[0].test_examples.len() equals `1`
   - Expected: groups[0].test_examples[0].description equals `adds numbers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers an example within a group")
step("Verify: registers an example within a group")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    it "adds numbers":
        # @req REQ-SSPEC-UNIT
        step("adds numbers")
        step("Verify: adds numbers")
        # @req: REQ-SPEC-Dsl-001
        nil

val groups = get_all_groups()
expect(groups[0].test_examples.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(groups[0].test_examples[0].description).to_equal("adds numbers")
```

</details>

#### can register multiple examples

- can register multiple examples
- Verify: can register multiple examples
- adds numbers
- Verify: adds numbers
- subtracts numbers
- Verify: subtracts numbers
   - Expected: groups[0].test_examples.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register multiple examples")
step("Verify: can register multiple examples")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    it "adds numbers":
        # @req REQ-SSPEC-UNIT
        step("adds numbers")
        step("Verify: adds numbers")
        # @req: REQ-SPEC-Dsl-001
        nil
    it "subtracts numbers":
        # @req REQ-SSPEC-UNIT
        step("subtracts numbers")
        step("Verify: subtracts numbers")
        # @req: REQ-SPEC-Dsl-001
        nil

val groups = get_all_groups()
expect(groups[0].test_examples.len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### executes the example block when run

- executes the example block when run
- Verify: executes the example block when run
- runs the block
- Verify: runs the block
   - Expected: executed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes the example block when run")
step("Verify: executes the example block when run")
# @req: REQ-SPEC-Dsl-001
var executed = false
describe "Test":
    it "runs the block":
        # @req REQ-SSPEC-UNIT
        step("runs the block")
        step("Verify: runs the block")
        # @req: REQ-SPEC-Dsl-001
        executed = true

val groups = get_all_groups()
groups[0].test_examples[0].run()
expect(executed).to_equal(true)
```

</details>

#### skip

#### registers a skipped example

- registers a skipped example
- Verify: registers a skipped example
   - Expected: example.is_skipped is true
   - Expected: example.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a skipped example")
step("Verify: registers a skipped example")
# @req: REQ-SPEC-Dsl-001
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

- registers a BeforeEach hook
- Verify: registers a BeforeEach hook
   - Expected: hooks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a BeforeEach hook")
step("Verify: registers a BeforeEach hook")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    before_each:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_before_each_hooks()
expect(hooks.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### can register multiple before_each hooks

- can register multiple before_each hooks
- Verify: can register multiple before_each hooks
   - Expected: groups[0].get_before_each_hooks().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register multiple before_each hooks")
step("Verify: can register multiple before_each hooks")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    before_each:
        nil
    before_each:
        nil

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### Hooks - after_each

#### registers an AfterEach hook

- registers an AfterEach hook
- Verify: registers an AfterEach hook
   - Expected: hooks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers an AfterEach hook")
step("Verify: registers an AfterEach hook")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    after_each:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_after_each_hooks()
expect(hooks.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### Hooks - before_all

#### registers a BeforeAll hook

- registers a BeforeAll hook
- Verify: registers a BeforeAll hook
   - Expected: hooks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a BeforeAll hook")
step("Verify: registers a BeforeAll hook")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    before_all:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_before_all_hooks()
expect(hooks.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### Hooks - after_all

#### registers an AfterAll hook

- registers an AfterAll hook
- Verify: registers an AfterAll hook
   - Expected: hooks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers an AfterAll hook")
step("Verify: registers an AfterAll hook")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    after_all:
        nil

val groups = get_all_groups()
val hooks = groups[0].get_after_all_hooks()
expect(hooks.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### let_lazy

#### registers a lazy memoized value

- registers a lazy memoized value
- Verify: registers a lazy memoized value
   - Expected: hooks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a lazy memoized value")
step("Verify: registers a lazy memoized value")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    let_lazy :value, \: 42

val groups = get_all_groups()
# let_lazy creates a before_each hook that sets up memoization
val hooks = groups[0].get_before_each_hooks()
expect(hooks.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### can register multiple lazy values

- can register multiple lazy values
- Verify: can register multiple lazy values
   - Expected: groups[0].get_before_each_hooks().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register multiple lazy values")
step("Verify: can register multiple lazy values")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    let_lazy :value1, \: 42
    let_lazy :value2, \: "hello"

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### given

#### registers an eager setup block as before_each

- registers an eager setup block as before_each
- Verify: registers an eager setup block as before_each
   - Expected: groups[0].get_before_each_hooks().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers an eager setup block as before_each")
step("Verify: registers an eager setup block as before_each")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    given:
        nil

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### can register multiple given blocks

- can register multiple given blocks
- Verify: can register multiple given blocks
   - Expected: groups[0].get_before_each_hooks().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register multiple given blocks")
step("Verify: can register multiple given blocks")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    given:
        nil
    given:
        nil

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### given_lazy

#### registers a lazy fixture in context definition

- registers a lazy fixture in context definition
- Verify: registers a lazy fixture in context definition
   - Expected: ctx_def.givens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a lazy fixture in context definition")
step("Verify: registers a lazy fixture in context definition")
# @req: REQ-SPEC-Dsl-001
context_def :test_context:
    given_lazy :data, \: "test data"

match get_context(:test_context):
    case Some(ctx_def):
        expect(ctx_def.givens.len()).to_equal(1)  # oracle: value fixed by the spec contract
    case None:
        fail("Expected context definition to be registered")
```

</details>

#### registers a before_each hook in regular context

- registers a before_each hook in regular context
- Verify: registers a before_each hook in regular context
   - Expected: groups[0].get_before_each_hooks().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a before_each hook in regular context")
step("Verify: registers a before_each hook in regular context")
# @req: REQ-SPEC-Dsl-001
describe "Test":
    given_lazy :user, \: "admin"

val groups = get_all_groups()
expect(groups[0].get_before_each_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### context_def

#### registers a reusable context definition

- registers a reusable context definition
- Verify: registers a reusable context definition
   - Expected: ctx_def.name.to_string() equals `admin_user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a reusable context definition")
step("Verify: registers a reusable context definition")
# @req: REQ-SPEC-Dsl-001
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

- can contain multiple givens
- Verify: can contain multiple givens
   - Expected: ctx_def.givens.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can contain multiple givens")
step("Verify: can contain multiple givens")
# @req: REQ-SPEC-Dsl-001
context_def :test_context:
    given:
        nil
    given_lazy :data, \: "test"

match get_context(:test_context):
    case Some(ctx_def):
        expect(ctx_def.givens.len()).to_equal(2)  # oracle: value fixed by the spec contract
    case None:
        fail("Expected context to be registered")
```

</details>

#### shared_examples

#### registers a shared example definition

- registers a shared example definition
- Verify: registers a shared example definition
- supports push
- Verify: supports push
   - Expected: shared_def.name equals `stack-like`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a shared example definition")
step("Verify: registers a shared example definition")
# @req: REQ-SPEC-Dsl-001
shared_examples "stack-like":
    it "supports push":
        # @req REQ-SSPEC-UNIT
        step("supports push")
        step("Verify: supports push")
        # @req: REQ-SPEC-Dsl-001
        nil

match get_shared_examples("stack-like"):
    case Some(shared_def):
        expect(shared_def.name).to_equal("stack-like")
    case None:
        fail("Expected shared example to be registered")
```

</details>

#### can have a description

- can have a description
- Verify: can have a description
   - Expected: desc equals `Container with stack operations`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can have a description")
step("Verify: can have a description")
# @req: REQ-SPEC-Dsl-001
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

- includes shared examples in current context
- Verify: includes shared examples in current context
- has size
- Verify: has size
   - Expected: array_group.children.len() equals `1`
   - Expected: array_group.children[0].description equals `behaves like collection-like`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes shared examples in current context")
step("Verify: includes shared examples in current context")
# @req: REQ-SPEC-Dsl-001
shared_examples "collection-like":
    it "has size":
        # @req REQ-SSPEC-UNIT
        step("has size")
        step("Verify: has size")
        # @req: REQ-SPEC-Dsl-001
        nil

describe "Array":
    it_behaves_like "collection-like"

val groups = get_all_groups()
val array_group = groups[0]
# it_behaves_like creates a nested context
expect(array_group.children.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(array_group.children[0].description).to_equal("behaves like collection-like")
```

</details>

#### shared examples have access to parent context

- shared examples have access to parent context
- Verify: shared examples have access to parent context
- adds numbers
- Verify: adds numbers
   - Expected: behaves_context.test_examples.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shared examples have access to parent context")
step("Verify: shared examples have access to parent context")
# @req: REQ-SPEC-Dsl-001
shared_examples "addable":
    it "adds numbers":
        # @req REQ-SSPEC-UNIT
        step("adds numbers")
        step("Verify: adds numbers")
        # @req: REQ-SPEC-Dsl-001
        # In real usage, this would access parent context helpers
        nil

describe "Calculator":
    it_behaves_like "addable"

val groups = get_all_groups()
val calc_group = groups[0]
val behaves_context = calc_group.children[0]
expect(behaves_context.test_examples.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### include_examples

#### is an alias for it_behaves_like

- is an alias for it_behaves_like
- Verify: is an alias for it_behaves_like
- supports each
- Verify: supports each
   - Expected: groups[0].children.len() equals `1`
   - Expected: groups[0].children[0].description equals `behaves like enumerable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is an alias for it_behaves_like")
step("Verify: is an alias for it_behaves_like")
# @req: REQ-SPEC-Dsl-001
shared_examples "enumerable":
    it "supports each":
        # @req REQ-SSPEC-UNIT
        step("supports each")
        step("Verify: supports each")
        # @req: REQ-SPEC-Dsl-001
        nil

describe "Array":
    include_examples "enumerable"

val groups = get_all_groups()
expect(groups[0].children.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(groups[0].children[0].description).to_equal("behaves like enumerable")
```

</details>

#### Full integration

#### supports complex nested structure with hooks and examples

- supports complex nested structure with hooks and examples
- Verify: supports complex nested structure with hooks and examples
- adds positive numbers
- Verify: adds positive numbers
- adds negative numbers
- Verify: adds negative numbers
- subtracts numbers
- Verify: subtracts numbers
   - Expected: calc.get_before_all_hooks().len() equals `1`
   - Expected: calc.get_before_each_hooks().len() equals `1`
   - Expected: calc.get_after_each_hooks().len() equals `1`
   - Expected: calc.get_after_all_hooks().len() equals `1`
   - Expected: calc.children.len() equals `2`
   - Expected: addition.description equals `addition`
   - Expected: addition.test_examples.len() equals `2`
   - Expected: addition.get_before_each_hooks().len() equals `1`
   - Expected: subtraction.description equals `subtraction`
   - Expected: subtraction.test_examples.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports complex nested structure with hooks and examples")
step("Verify: supports complex nested structure with hooks and examples")
# @req: REQ-SPEC-Dsl-001
describe "Calculator":
    before_all:
        nil
    before_each:
        nil

    context "addition":
        before_each:
            nil

        it "adds positive numbers":
            # @req REQ-SSPEC-UNIT
            step("adds positive numbers")
            step("Verify: adds positive numbers")
            # @req: REQ-SPEC-Dsl-001
            nil

        it "adds negative numbers":
            # @req REQ-SSPEC-UNIT
            step("adds negative numbers")
            step("Verify: adds negative numbers")
            # @req: REQ-SPEC-Dsl-001
            nil

    context "subtraction":
        it "subtracts numbers":
            # @req REQ-SSPEC-UNIT
            step("subtracts numbers")
            step("Verify: subtracts numbers")
            # @req: REQ-SPEC-Dsl-001
            nil

    after_each:
        nil
    after_all:
        nil

val groups = get_all_groups()
val calc = groups[0]

# Check top-level hooks
expect(calc.get_before_all_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(calc.get_before_each_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(calc.get_after_each_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(calc.get_after_all_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract

# Check nested contexts
expect(calc.children.len()).to_equal(2)  # oracle: value fixed by the spec contract

# Check addition context
val addition = calc.children[0]
expect(addition.description).to_equal("addition")
expect(addition.test_examples.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(addition.get_before_each_hooks().len()).to_equal(1)  # oracle: value fixed by the spec contract

# Check subtraction context
val subtraction = calc.children[1]
expect(subtraction.description).to_equal("subtraction")
expect(subtraction.test_examples.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SPEC-Dsl-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `844f15d8f18c4c033333534c7f9c9d72cb5d22f967682c10d0ba6527f9b8166e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `844f15d8f18c4c033333534c7f9c9d72cb5d22f967682c10d0ba6527f9b8166e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `844f15d8f18c4c033333534c7f9c9d72cb5d22f967682c10d0ba6527f9b8166e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **81/100**; blockers: **0**.

SSpec documentization score: 81/100
source: test/unit/spec/dsl_spec.spl
mirror: doc/06_spec/unit/spec/dsl_spec.md (current)
findings: 16 blockers: 0
  narrative=100 structure=30 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/spec/dsl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/spec/dsl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/spec/dsl_spec.spl:1:1: advice SSDOC-MNT-006 [maintainability] (-10): repeated setup is not expressed through a named helper
  why: Named setup helpers keep scenarios concise and consistent.
  improve: Extract a domain-named setup helper shared by the scenarios.
test/unit/spec/dsl_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers a top-level example group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/dsl_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can contain nested contexts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/dsl_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can contain nested contexts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/dsl_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can contain multiple nested contexts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/dsl_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can contain multiple nested contexts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/dsl_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be nested multiple levels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/dsl_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register multiple examples' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/dsl_spec.spl:184:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'registers an ignored example' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/spec/dsl_spec.spl:186:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'takes a long time' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/spec/dsl_spec.spl:193:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ignored tests are never run' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/spec/dsl_spec.spl:196:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'takes forever' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/spec/dsl_spec.spl:218:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register multiple before_each hooks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/dsl_spec.spl:288:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register multiple lazy values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
