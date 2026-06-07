# Lean Basic Specification

> 1. var emit = emitter LeanEmitter new

<!-- sdn-diagram:id=lean_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_basic_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Basic Specification

## Scenarios

### Lean Basic

#### LeanEmitter

#### emits indented lines

1. var emit = emitter LeanEmitter new
2. emit emit line
3. emit indent
4. emit emit line
5. emit emit line
6. emit dedent


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var emit = emitter.LeanEmitter.new()
emit.emit_line("structure Foo where")
emit.indent()
emit.emit_line("x : Int")
emit.emit_line("y : Bool")
emit.dedent()

val output = emit.finish()
expect(output).to_contain("structure Foo where")
expect(output).to_contain("  x : Int")
expect(output).to_contain("  y : Bool")
```

</details>

#### renders structure and theorem helpers

1. var emit = emitter LeanEmitter new
2. emit emit structure data
3. emit emit theorem data


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var emit = emitter.LeanEmitter.new()
emit.emit_structure_data("Point", [("x", "Int"), ("y", "Int")], ["Repr"])
emit.emit_theorem_data("point_eq", [("x", "Int")], "x = x", Some("rfl"), false)

val output = emit.finish()
expect(output).to_contain("structure Point where")
expect(output).to_contain("deriving Repr")
expect(output).to_contain("theorem point_eq")
expect(output).to_contain("rfl")
```

</details>

#### Naming conventions

#### translates module and identifier names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_pascal_case("my_type")).to_equal("MyType")
expect(naming.to_camel_case("get_value")).to_equal("getValue")
expect(naming.to_lean_namespace("std.collections")).to_equal("Std.Collections")
expect(naming.to_lean_ident("my var")).to_equal("my_var")
```

</details>

#### detects and escapes reserved words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.is_reserved("let")).to_equal(true)
expect(naming.is_reserved("myVar")).to_equal(false)
expect(naming.sanitize_lean_ident("def")).to_equal("«def»")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/lean_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Basic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
