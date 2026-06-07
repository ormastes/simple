# Atom Specification

> <details>

<!-- sdn-diagram:id=atom_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=atom_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

atom_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=atom_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atom Specification

## Scenarios

### atom literals

#### atom is a text value with backtick prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_atom("hello")
expect(a).to_equal("`hello")
```

</details>

#### two atoms with same name are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_atom("foo")
val b = make_atom("foo")
expect(atom_eq(a, b)).to_equal(true)
```

</details>

#### two atoms with different names are not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_atom("foo")
val b = make_atom("bar")
val not_equal = a != b
expect(not_equal).to_equal(true)
```

</details>

#### atom can be used in match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = make_atom("running")
val result = match state:
    case "`running": "is running"
    case "`stopped": "is stopped"
    case _: "unknown"
expect(result).to_equal("is running")
```

</details>

#### atom used as map key works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val active = make_atom("active")
val inactive = make_atom("inactive")
val m = {"`active": true, "`inactive": false}
expect(m[active]).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/atom_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- atom literals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
