# Object Mapper Specification

> 1. var mapper = SharedExecMapper new

<!-- sdn-diagram:id=object_mapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=object_mapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

object_mapper_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=object_mapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Mapper Specification

## Scenarios

### Object Mapper

#### maps and looks up symbols

1. var mapper = SharedExecMapper new
   - Expected: mapped.is_ok() is true
   - Expected: mapper.lookup("fn_a").? is true
   - Expected: mapper.get_record("fn_a").unwrap().owner_id equals `module_a`
   - Expected: mapper.stats().mapped_symbols equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mapper = SharedExecMapper.new(SharedExecMapperConfig(verbose: false))
val mapped = mapper.map_symbol("module_a", "fn_a", tiny_code(), false)

expect(mapped.is_ok()).to_equal(true)
expect(mapper.lookup("fn_a").?).to_equal(true)
expect(mapper.get_record("fn_a").unwrap().owner_id).to_equal("module_a")
expect(mapper.stats().mapped_symbols).to_equal(1)
```

</details>

#### rejects duplicate mappings when replacement is disabled

1. var mapper = SharedExecMapper new
   - Expected: mapper.map_symbol("module_a", "dup_fn", tiny_code(), false).is_ok() is true
   - Expected: mapper.map_symbol("module_a", "dup_fn", tiny_code(), false).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mapper = SharedExecMapper.new(SharedExecMapperConfig(verbose: false))
expect(mapper.map_symbol("module_a", "dup_fn", tiny_code(), false).is_ok()).to_equal(true)
expect(mapper.map_symbol("module_a", "dup_fn", tiny_code(), false).is_err()).to_equal(true)
```

</details>

#### replaces existing mappings when replacement is enabled

1. var mapper = SharedExecMapper new
2.   = mapper map symbol
   - Expected: replaced.is_ok() is true
   - Expected: mapper.get_record("replace_fn").unwrap().generation equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mapper = SharedExecMapper.new(SharedExecMapperConfig(verbose: false))
_ = mapper.map_symbol("module_a", "replace_fn", tiny_code(), false)
val replaced = mapper.map_symbol("module_a", "replace_fn", [144, 195], true)

expect(replaced.is_ok()).to_equal(true)
expect(mapper.get_record("replace_fn").unwrap().generation).to_equal(2)
```

</details>

#### unmaps all symbols for a specific owner

1. var mapper = SharedExecMapper new
2.   = mapper map symbol
3.   = mapper map symbol
4.   = mapper map symbol
   - Expected: mapper.unmap_owner("owner_a") equals `2`
   - Expected: mapper.lookup("a1").? is false
   - Expected: mapper.lookup("b1").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mapper = SharedExecMapper.new(SharedExecMapperConfig(verbose: false))
_ = mapper.map_symbol("owner_a", "a1", tiny_code(), false)
_ = mapper.map_symbol("owner_a", "a2", tiny_code(), false)
_ = mapper.map_symbol("owner_b", "b1", tiny_code(), false)

expect(mapper.unmap_owner("owner_a")).to_equal(2)
expect(mapper.lookup("a1").?).to_equal(false)
expect(mapper.lookup("b1").?).to_equal(true)
```

</details>

#### enforces loader replacement policy

1. var mapper = SharedExecMapper new
2.   = loader mapper map
   - Expected: denied.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mapper = SharedExecMapper.new(SharedExecMapperConfig(verbose: false))
val loader_mapper = LoaderMapper.new(LoaderMapperConfig(allow_replace_on_reload: false))

_ = loader_mapper.map(mapper, "module_a", "sym", tiny_code(), false)
val denied = loader_mapper.map(mapper, "module_a", "sym", [144, 195], true)
expect(denied.is_err()).to_equal(true)
```

</details>

#### uses the JIT default owner when none is provided

1. var mapper = SharedExecMapper new
   - Expected: mapped.is_ok() is true
   - Expected: mapper.get_record("jit_fn").unwrap().owner_id equals `__jit__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mapper = SharedExecMapper.new(SharedExecMapperConfig(verbose: false))
val jit_mapper = JitMapper.new(JitMapperConfig(default_owner: "__jit__", allow_replace: true))

val mapped = jit_mapper.map(mapper, "", "jit_fn", tiny_code())
expect(mapped.is_ok()).to_equal(true)
expect(mapper.get_record("jit_fn").unwrap().owner_id).to_equal("__jit__")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/object_mapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Object Mapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
