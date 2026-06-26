# Ponytail Audit Specification

> <details>

<!-- sdn-diagram:id=ponytail_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ponytail_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ponytail_audit_spec -> std
ponytail_audit_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ponytail_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ponytail Audit Specification

## Scenarios

### ponytail audit

#### renders clean audit output

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_ponytail_fixture("clean", "fn hello() -> text:\n    \"ok\"\n")
val output = ponytail_audit(path)
expect(output).to_contain("Ponytail Audit")
expect(output).to_contain("status: ok")
expect_absence_marker_hidden(output)
```

</details>

#### flags placeholder and abstraction markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_ponytail_fixture("smells", "interface FutureThing:\n    pass_todo\n")
val output = ponytail_audit(path)
expect(output).to_contain("status: review")
expect(output).to_contain("placeholder markers:")
expect(output).to_contain("abstraction smells:")
```

</details>

#### returns explicit missing status for absent source

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = ponytail_audit("build/test/ponytail/missing.spl")
expect(output).to_contain("status: missing")
expect(output).to_contain("reason: source unavailable")
expect_absence_marker_hidden(output)
```

</details>

#### renders simplification report suggestions

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_ponytail_fixture("report", "interface FutureThing:\n    pass_todo\n    # TODO simplify\n")
val output = ponytail_simplification_report(path)
expect(output).to_contain("Ponytail Simplification Report")
expect(output).to_contain("status: review")
expect(output).to_contain("cut placeholder passes:")
expect(output).to_contain("cut speculative abstraction:")
expect(output).to_contain("resolve todo markers:")
expect(output).to_contain("total_suggestions:")
expect_absence_marker_hidden(output)
```

</details>

#### renders clean simplification report without suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_ponytail_fixture("report_clean", "fn hello() -> text:\n    \"ok\"\n")
val output = ponytail_simplification_report(path)
expect(output).to_contain("status: ok")
expect(output).to_contain("summary: no simplification targets found")
expect(output).to_contain("total_suggestions: 0")
```

</details>

#### renders missing simplification report as explicit absence

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = ponytail_simplification_report("build/test/ponytail/report_missing.spl")
expect(output).to_contain("status: missing")
expect(output).to_contain("reason: source unavailable")
expect(output).to_contain("total_suggestions: 0")
expect_absence_marker_hidden(output)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/ponytail_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ponytail audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
