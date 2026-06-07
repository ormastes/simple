# Wine Pe Gate Specification

> <details>

<!-- sdn-diagram:id=wine_pe_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_pe_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_pe_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_pe_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Pe Gate Specification

## Scenarios

### Wine PE loader gate

### loader feature coverage

#### lists PE validation features needed before hello.exe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = wine_pe_required_features()
expect(required.len()).to_be_greater_than(10)
expect(required[0]).to_equal("mz")
```

</details>

#### reports the first missing PE loader feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_pe_gate("mz pe-signature machine-x86_64 pe32plus")
expect(state).to_equal("missing-section-bounds")
```

</details>

#### returns ready for the full safe parse/map feature set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_pe_gate("mz pe-signature machine-x86_64 pe32plus section-bounds console-subsystem imports relocations tls-directory structured-errors safe-map no-exec-before-gates")
expect(state).to_equal("ready")
```

</details>

#### derives PE readiness from actual image bytes and loader policies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_pe_gate_from_image(_image(), "native-module-open tls-callback", "structured-errors safe-map no-exec-before-gates")
expect(state).to_equal("ready")
```

</details>

#### keeps image-backed PE readiness blocked on structured loader policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_pe_gate_from_image(_image(), "native-module-open tls-callback", "structured-errors safe-map")).to_equal("missing-no-exec-before-gates")
expect(wine_pe_gate_from_image(_image(), "native-module-open", "structured-errors safe-map no-exec-before-gates")).to_equal("missing-api-tls-callback")
```

</details>

### header classification

#### rejects non-MZ inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_pe_header_gate("not-pe")).to_equal("bad-mz")
```

</details>

#### accepts a declared PE32+ x86_64 console header summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = "MZ PE x86_64 PE32+ console"
expect(wine_pe_header_gate(summary)).to_equal("ready")
```

</details>

### execution gate

#### blocks execution until process, VM, host, and PE gates are verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_pe_execution_gate("process=verified vm=verified host=partial pe=verified")
expect(state).to_equal("blocked-host")
```

</details>

#### requires async and thread gates before PE execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_pe_execution_gate("process=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe=verified")
expect(state).to_equal("blocked-async")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_pe_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine PE loader gate
- loader feature coverage
- header classification
- execution gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
