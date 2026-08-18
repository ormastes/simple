# Calc Session Host Isolation Specification

> Tests covering Calc session host production isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Calc Session Host Isolation Specification

## Scenarios

### Calc session host production isolation

#### keeps the normal terminal owner free of access and capture transports

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/app/office/sheets/calc_session_host.spl").lower()
expect(source.contains("app.ui.standalone")).to_be(false)
expect(source.contains("test_api")).to_be(false)
expect(source.contains("tcp")).to_be(false)
expect(source.contains("sgtti")).to_be(false)
expect(source.contains("capture")).to_be(false)
```

</details>

<details>
<summary>Advanced: confines loopback transport to the explicit access adapter</summary>

#### confines loopback transport to the explicit access adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/app/office/sheets/calc_access_session_host.spl")
expect(source).to_contain("app.ui.standalone.bootstrap")
expect(source).to_contain("TcpListener")
expect(source).to_contain("CalcSessionHost")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/calc_session_host_isolation_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Calc session host production isolation.
- Calc session host production isolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
