# Discovery Specification

> <details>

<!-- sdn-diagram:id=discovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=discovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

discovery_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=discovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Discovery Specification

## Scenarios

### Doctest Source Parsing

#### parse_doctests integration

#### discovers doctests in doc comments

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "/// Example usage:\n/// >>> 1 + 2\n/// 3\nfn add(a: i64, b: i64) -> i64:\n    a + b\n"
val items = parse_doctests(source, "lib/math.spl")

expect items.len to eq 1
expect items[0].commands to eq ["1 + 2"]
expect items[0].source_path to eq "lib/math.spl"
```

</details>

#### discovers multiple doctests across functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "/// >>> 1 + 1\n/// 2\nfn foo(): pass\n\n/// >>> 2 + 2\n/// 4\nfn bar(): pass\n"
val items = parse_doctests(source, "lib/ops.spl")

expect items.len to eq 2
expect items[0].commands to eq ["1 + 1"]
expect items[1].commands to eq ["2 + 2"]
```

</details>

#### skips functions without doc comments

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn helper(): pass\n\n/// >>> 42\n/// 42\nfn documented(): pass\n"
val items = parse_doctests(source, "lib/mixed.spl")

expect items.len to eq 1
expect items[0].commands to eq ["42"]
```

</details>

#### handles exception expectations in doc comments

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "/// >>> bad_call()\n/// Error: ValueError\nfn risky(): pass\n"
val items = parse_doctests(source, "lib/errors.spl")

expect items.len to eq 1
match items[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
    case _:
        fail "Expected Exception"
```

</details>

#### preserves line numbers

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# header\n\n/// >>> 1\n/// 1\nfn f(): pass\n"
val items = parse_doctests(source, "test.spl")

expect items.len to eq 1
expect items[0].start_line to eq 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/doctest/discovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Doctest Source Parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
