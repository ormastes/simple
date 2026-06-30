# Environment Specification

> <details>

<!-- sdn-diagram:id=environment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=environment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

environment_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=environment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Environment Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/core/environment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Binding

#### stores name, value, and mutability

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = Binding(name: "x", value: "42", mutable: true)
expect(binding.mutable).to_equal(true)
expect(binding.name_str()).to_equal("x")
expect(binding.value).to_equal("42")
```

</details>

### Scope

#### creates an empty scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = Scope.new()
match scope.parent:
    case nil: expect(scope.bindings.len()).to_equal(0)
    case Some(_): fail("new scope should not have a parent")
```

</details>

#### creates scope with parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = Scope.new()
val child = Scope.with_parent(parent)
match child.parent:
    case Some(parent_scope): expect(parent_scope.bindings.len()).to_equal(0)
    case nil: fail("child scope should keep parent")
```

</details>

#### defines and retrieves values

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = Scope.new().define("x", "42", true)
match scope.get("x"):
    case Some(binding):
        expect(binding.value).to_equal("42")
        expect(binding.mutable).to_equal(true)
    case nil:
        fail("unexpected environment result branch")
```

</details>

#### searches parent scope

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = Scope.new().define("outer", "10", true)
val child = Scope.with_parent(parent)
match child.get("outer"):
    case Some(binding):
        expect(binding.value).to_equal("10")
    case nil:
        fail("unexpected environment result branch")
```

</details>

#### updates mutable bindings

- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = Scope.new().define("count", "1", true)
match scope.set("count", "2"):
    case Ok(updated):
        match updated.get("count"):
            case Some(binding):
                expect(binding.value).to_equal("2")
            case nil:
                fail("unexpected environment result branch")
    case Err(_):
        fail("unexpected environment result branch")
```

</details>

#### rejects immutable bindings

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = Scope.new().define("pi", "3.14", false)
match scope.set("pi", "3.14159"):
    case Err(msg):
        expect(msg).to_equal("immutable binding")
    case Ok(_):
        fail("unexpected environment result branch")
```

</details>

#### returns error for missing bindings

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = Scope.new()
match scope.set("missing", "1"):
    case Err(msg):
        expect(msg).to_equal("Undefined variable")
    case Ok(_):
        fail("unexpected environment result branch")
```

</details>

### Environment

#### creates a root scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = Environment.new()
expect(env.scopes.len()).to_equal(1)
```

</details>

#### pushes and pops scopes

- var env = Environment new
- env push scope
   - Expected: env.scopes.len() equals `2`
- env pop scope
   - Expected: env.scopes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = Environment.new()
env.push_scope()
expect(env.scopes.len()).to_equal(2)
env.pop_scope()
expect(env.scopes.len()).to_equal(1)
```

</details>

#### keeps root scope when popping once

- var env = Environment new
- env pop scope
   - Expected: env.scopes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = Environment.new()
env.pop_scope()
expect(env.scopes.len()).to_equal(1)
```

</details>

#### defines global values

- var env = Environment new
- env define global
   - Expected: binding.value equals `yes`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = Environment.new()
env.define_global("global", "yes")
match env.get("global"):
    case Some(binding):
        expect(binding.value).to_equal("yes")
    case nil:
        fail("unexpected environment result branch")
```

</details>

#### updates the current scope

- var env = Environment new
- env define
   - Expected: binding.value equals `2`
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = Environment.new()
env.define("local", "1")
match env.set("local", "2"):
    case Ok(_):
        match env.get("local"):
            case Some(binding):
                expect(binding.value).to_equal("2")
            case nil:
                fail("unexpected environment result branch")
    case Err(_):
        fail("unexpected environment result branch")
```

</details>

#### searches parent chain after pushing

- var env = Environment new
- env define
- env push scope
- env define
   - Expected: binding.value equals `10`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = Environment.new()
env.define("outer", "10")
env.push_scope()
env.define("inner", "20")
match env.get("outer"):
    case Some(binding):
        expect(binding.value).to_equal("10")
    case nil:
        fail("unexpected environment result branch")
```

</details>

### EnvironmentWithInterner

#### interns and resolves names

- var env = EnvironmentWithInterner new
   - Expected: sym.id > 0 is true
   - Expected: name equals `alpha`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = EnvironmentWithInterner.new()
val sym = env.intern("alpha")
expect(sym.id > 0).to_equal(true)
match EnvironmentWithInterner.resolve(sym):
    case Some(name):
        expect(name).to_equal("alpha")
    case nil:
        fail("unexpected environment result branch")
```

</details>

#### reuses the same symbol for the same text

- var env = EnvironmentWithInterner new
   - Expected: first.id equals `second.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = EnvironmentWithInterner.new()
val first = env.intern("beta")
val second = env.intern("beta")
expect(first.id).to_equal(second.id)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
