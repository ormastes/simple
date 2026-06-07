# I18n Context Specification

> <details>

<!-- sdn-diagram:id=i18n_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=i18n_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

i18n_context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=i18n_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I18n Context Specification

## Scenarios

### I18N Context

#### keeps compiler diagnostics independent from full i18n formatters

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_init_source()

expect(source).to_contain("Minimal diagnostic system without i18n or formatters.")
expect(source).to_contain("Used by the parser and compiler to avoid circular dependencies.")
expect(source).to_contain("For full diagnostics with i18n and formatters, use the lib.diagnostics module.")
expect(source).to_contain("export severity.Severity")
expect(source).to_contain("export diagnostic.Diagnostic")
```

</details>

#### keeps i18n command stub explicit when SFFI support is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = io_stub_source()

expect(source).to_contain("fn cli_run_i18n(args: [text]) -> i64")
expect(source).to_contain("Error: i18n requires Rust SFFI support")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/diagnostics/i18n_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- I18N Context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
