# Const Specification

> <details>

<!-- sdn-diagram:id=const_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=const_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

const_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=const_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Specification

## Scenarios

### const declarations

#### parses module const declarations as value bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = parse_const_decls(
    "const MAX_SIZE = 100\n" +
    "const PI = 3.14159\n" +
    "const APP_NAME = \"Simple\"\n" +
    "const ENABLED = true\n" +
    "const ZERO = 0\n"
)

expect(decls.len()).to_equal(5)
expect(decl_get_tag(decls[0])).to_equal(DECL_VAL)
expect(decl_get_name(decls[0])).to_equal("MAX_SIZE")
expect(decl_get_name(decls[1])).to_equal("PI")
expect(decl_get_name(decls[2])).to_equal("APP_NAME")
expect(decl_get_name(decls[3])).to_equal("ENABLED")
expect(decl_get_name(decls[4])).to_equal("ZERO")
```

</details>

#### keeps const initializer expressions on declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = parse_const_decls("const MAX_SIZE = 100\nconst APP_NAME = \"Simple\"\n")

expect(decl_get_body(decls[0]).len()).to_equal(1)
expect(decl_get_body(decls[1]).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/const_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- const declarations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
