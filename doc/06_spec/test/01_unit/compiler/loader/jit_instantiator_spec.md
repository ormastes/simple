# Jit Instantiator Specification

> <details>

<!-- sdn-diagram:id=jit_instantiator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_instantiator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_instantiator_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_instantiator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Instantiator Specification

## Scenarios

### Jit Instantiator

#### reports empty stats for a new instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = JitInstantiator.new(default_jit_config())
val stats = jit.stats()
expect(stats.cached_count).to_equal(0)
expect(stats.compile_count).to_equal(0)
expect(stats.loaded_smf_count).to_equal(0)
```

</details>

#### finds metadata-backed symbols

1. var jit = JitInstantiator new
2. jit set metadata for test
   - Expected: jit.can_jit_instantiate("Vec$i64") is true
   - Expected: found.? is true
   - Expected: found.unwrap()[0] equals `vec.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(default_jit_config())
val entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "Vec$i64"
)
jit.set_metadata_for_test("vec.smf", LoadedMetadata(possible: [entry], instantiations: []))

expect(jit.can_jit_instantiate("Vec$i64")).to_equal(true)
val found = jit.find_possible("Vec$i64")
expect(found.?).to_equal(true)
expect(found.unwrap()[0]).to_equal("vec.smf")
```

</details>

#### returns cached code without changing depth

1. var jit = JitInstantiator new
2. jit set cache for test
   - Expected: code equals `[1, 2, 3]`
   - Expected: symbol equals `cached_fn`
   - Expected: address.unwrap() equals `4096`
3. fail
   - Expected: jit.depth equals `before_depth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(default_jit_config())
jit.set_cache_for_test("cached_fn", [1, 2, 3], 4096)
val before_depth = jit.depth

val result = jit.try_jit_instantiate("cached_fn")
match result:
    case JitInstantiationResult.Success(code, symbol, address):
        expect(code).to_equal([1, 2, 3])
        expect(symbol).to_equal("cached_fn")
        expect(address.unwrap()).to_equal(4096)
    case _:
        fail("expected cached success")

expect(jit.depth).to_equal(before_depth)
```

</details>

#### compiles known metadata-backed symbols and records the instantiation

1. var jit = JitInstantiator new
2. jit set metadata for test
   - Expected: symbol equals `Map$text_i64`
   - Expected: address.? is true
3. fail
   - Expected: jit.in_progress does not contain `Map$text_i64`
   - Expected: jit.depth equals `0`
   - Expected: jit.stats().compile_count equals `1`
   - Expected: jit.loaded_metadata["map.smf"].possible.len() equals `0`
   - Expected: jit.loaded_metadata["map.smf"].instantiations.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(default_jit_config())
val entry = PossibleInstantiation(
    template_name: "Map",
    type_args: "text,i64",
    mangled_name: "Map$text_i64"
)
jit.set_metadata_for_test("map.smf", LoadedMetadata(possible: [entry], instantiations: []))

val result = jit.try_jit_instantiate("Map$text_i64")
match result:
    case JitInstantiationResult.Success(code, symbol, address):
        expect(symbol).to_equal("Map$text_i64")
        expect(code.len()).to_be_greater_than(0)
        expect(address.?).to_equal(true)
    case _:
        fail("expected compile success")

expect(jit.in_progress.contains("Map$text_i64")).to_equal(false)
expect(jit.depth).to_equal(0)
expect(jit.stats().compile_count).to_equal(1)
expect(jit.loaded_metadata["map.smf"].possible.len()).to_equal(0)
expect(jit.loaded_metadata["map.smf"].instantiations.len()).to_equal(1)
```

</details>

#### detects direct circular dependencies

1. var jit = JitInstantiator new
2. jit in progress = jit in progress insert
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(default_jit_config())
jit.in_progress = jit.in_progress.insert("cycle_fn")

val result = jit.try_jit_instantiate("cycle_fn")
match result:
    case JitInstantiationResult.CircularDependency(cycle):
        expect(cycle.len()).to_be_greater_than(0)
    case _:
        fail("expected circular dependency")
```

</details>

#### enforces the configured depth limit

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig(
    update_smf: true,
    max_depth: 2,
    enabled: true,
    verbose: false
))
jit.depth = 2

val result = jit.try_jit_instantiate("too_deep")
match result:
    case JitInstantiationResult.CompilationError(message):
        expect(message).to_contain("Maximum JIT depth")
    case _:
        fail("expected depth error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/jit_instantiator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jit Instantiator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
