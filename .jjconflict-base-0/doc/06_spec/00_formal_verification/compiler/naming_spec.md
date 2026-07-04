# Naming Specification

> <details>

<!-- sdn-diagram:id=naming_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=naming_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

naming_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=naming_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Naming Specification

## Scenarios

### Lean Naming Conventions

#### PascalCase

#### converts snake case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_pascal_case("ref_capability")).to_equal("RefCapability")
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_pascal_case("")).to_equal("")
```

</details>

#### camelCase

#### converts snake case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_camel_case("get_value")).to_equal("getValue")
```

</details>

#### lowercases the first character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_camel_case("UPPER")).to_equal("uPPER")
```

</details>

#### reserved words

#### detects Lean keywords

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.is_reserved("let")).to_equal(true)
expect(naming.is_reserved("forall")).to_equal(true)
expect(naming.is_reserved("myFunction")).to_equal(false)
```

</details>

#### escapes reserved identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.sanitize_lean_ident("def")).to_equal("«def»")
expect(naming.sanitize_lean_ident("myVar")).to_equal("myVar")
```

</details>

#### Lean name helpers

#### converts type names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_lean_type_name("my_type")).to_equal("MyType")
expect(naming.to_lean_type_name("type")).to_equal("«Type»")
```

</details>

#### converts function names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_lean_func_name("my_function")).to_equal("myFunction")
expect(naming.to_lean_func_name("let")).to_equal("«let»")
```

</details>

#### converts namespaces and identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(naming.to_lean_namespace("std.collections")).to_equal("Std.Collections")
expect(naming.to_lean_ident("my-var")).to_equal("my_var")
expect(naming.to_lean_ident("123abc")).to_equal("_123abc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/naming_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Naming Conventions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
