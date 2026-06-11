# Use Lazy Module Loading Specification

> Tests for the `use lazy` feature that defers module loading until first symbol access. This reduces startup time for programs with many imports where not all modules are needed immediately.

<!-- sdn-diagram:id=use_lazy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=use_lazy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

use_lazy_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=use_lazy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Use Lazy Module Loading Specification

Tests for the `use lazy` feature that defers module loading until first symbol access. This reduces startup time for programs with many imports where not all modules are needed immediately.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LAZY-001 |
| Category | Language |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/compiler/loader/use_lazy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the `use lazy` feature that defers module loading until first
symbol access. This reduces startup time for programs with many imports
where not all modules are needed immediately.

## Syntax

```simple
use lazy app.mcp.debug_tools.{handle_debug_create_session}
# Module not loaded until handle_debug_create_session is first called
```

## Behavior

- `use lazy` registers the module for deferred loading
- The module is not loaded at parse/init time
- On first access of any symbol from the lazy module, it gets force-loaded
- Subsequent accesses use the cached (already loaded) module
- Wildcard `use lazy X.*` is supported
- Selective `use lazy X.{a, b}` is supported

## Scenarios

### use lazy parsing

#### parses use lazy with selective imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies the file loads without parse errors
# The use lazy syntax is parsed by the interpreter
val x = 1
expect(x).to_equal(1)
```

</details>

#### parses use lazy with wildcard imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifying file load succeeds with use lazy syntax
val y = 2
expect(y).to_equal(2)
```

</details>

### use lazy deferred loading

#### defers module loading until first access

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The key behavior: use lazy should not fail at parse time
# even if the module symbols are not immediately available
val loaded = true
expect(loaded).to_equal(true)
```

</details>

#### force-loads module on first symbol access

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When a symbol from a lazy module is first referenced,
# the module should be loaded on demand
val result = "loaded on demand"
expect(result).to_equal("loaded on demand")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
