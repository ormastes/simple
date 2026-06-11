# Keyword Only Params Specification

> <details>

<!-- sdn-diagram:id=keyword_only_params_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=keyword_only_params_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

keyword_only_params_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=keyword_only_params_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keyword Only Params Specification

## Scenarios

### keyword-only params (~)

#### function with named params is callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = greet(name: "Alice", greeting: "Hello")
expect(result).to_equal("Hello, Alice!")
```

</details>

#### mixed positional and named params work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = configure("example.com", 443, false)
expect(result).to_equal("example.com:443")
```

</details>

#### keyword-only param with debug enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = configure("localhost", 8080, true)
expect(result).to_equal("localhost:8080 [debug]")
```

</details>

#### named params in any order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = greet(greeting: "Hi", name: "Bob")
expect(result).to_equal("Hi, Bob!")
```

</details>

#### simple add function with named params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add(a: 3, b: 4)
expect(result).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/keyword_only_params_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- keyword-only params (~)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
