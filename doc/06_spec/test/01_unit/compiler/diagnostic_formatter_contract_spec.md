# Diagnostic Formatter Contract Specification

> 1.  with code

<!-- sdn-diagram:id=diagnostic_formatter_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagnostic_formatter_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagnostic_formatter_contract_spec -> compiler
diagnostic_formatter_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagnostic_formatter_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostic Formatter Contract Specification

## Scenarios

### diagnostic formatter production contract

#### renders code span label note and help in Simple syntax

1.  with code
2.  with span
3.  with label
4.  with note
5.  with help


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.new(4, 9, 2, 5)
val diagnostic = Diagnostic.error("Unknown method 'push' for String")
    .with_code("E1003")
    .with_span(span)
    .with_label(span, "receiver has type String")
    .with_note("StringBuilder supports append")
    .with_help("Use append on a StringBuilder")

val formatted = SimpleFormatter.new().format(diagnostic)

expect(formatted).to_contain("code: \"E1003\"")
expect(formatted).to_contain("message: \"Unknown method 'push' for String\"")
expect(formatted).to_contain("span: Span(start: 4, end: 9, line: 2, column: 5)")
expect(formatted).to_contain("receiver has type String")
expect(formatted).to_contain("StringBuilder supports append")
expect(formatted).to_contain("help: \"Use append on a StringBuilder\"")
```

</details>

#### renders code span label note and help in JSON

1.  with code
2.  with span
3.  with label
4.  with note
5.  with help


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.new(10, 18, 3, 7)
val diagnostic = Diagnostic.warning("deprecated API")
    .with_code("W0406")
    .with_span(span)
    .with_label(span, "wildcard import")
    .with_note("explicit imports are preferred")
    .with_help("Import the named symbols")

val formatted = JsonFormatter.new().format(diagnostic)

expect(formatted).to_contain("\"severity\":\"warning\"")
expect(formatted).to_contain("\"message\":\"deprecated API\"")
expect(formatted).to_contain("\"code\":\"W0406\"")
expect(formatted).to_contain("\"line\":3")
expect(formatted).to_contain("\"column\":7")
expect(formatted).to_contain("\"wildcard import\"")
expect(formatted).to_contain("\"explicit imports are preferred\"")
expect(formatted).to_contain("\"help\":\"Import the named symbols\"")
```

</details>

#### renders code span label note and help in terminal text

1.  with code
2.  with span
3.  with label
4.  with note
5.  with help


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.new(5, 11, 2, 3)
val diagnostic = Diagnostic.error("expected expression")
    .with_code("E0001")
    .with_span(span)
    .with_label(span, "expression starts here")
    .with_note("parser stopped before a complete expression")
    .with_help("Add a value or remove the operator")

val source = "let x =\n  + 1\n"
val formatted = TextFormatter.without_color().format(diagnostic, source)

expect(formatted).to_contain("error[E0001]: expected expression")
expect(formatted).to_contain("--> <source>:2:3")
expect(formatted).to_contain("expression starts here")
expect(formatted).to_contain("note: parser stopped before a complete expression")
expect(formatted).to_contain("help: Add a value or remove the operator")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/diagnostic_formatter_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diagnostic formatter production contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
