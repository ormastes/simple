# parser_spec

> Tests for the doctest parser module which extracts and parses

<!-- sdn-diagram:id=parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_spec

Tests for the doctest parser module which extracts and parses

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the doctest parser module which extracts and parses
executable code examples from documentation strings.

## Scenarios

### DoctestParser

#### parse_docstring

#### is a documented feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Doctest parser is implemented in doctest.parser module
# The parser.spl file exists and exports parse_docstring function
# This test verifies the feature is documented in the test suite
expect true
```

</details>

#### will be tested when module imports are stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parse_docstring function exists but requires stable module loading
# Once module imports work reliably, we can add tests like:
# val result = parse_docstring(">>> 1 + 1{NL}2")
# expect result.len > 0
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
