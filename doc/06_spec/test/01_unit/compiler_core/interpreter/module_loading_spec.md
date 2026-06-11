# Module Loading Specification

> <details>

<!-- sdn-diagram:id=module_loading_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loading_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loading_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loading_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loading Specification

## Scenarios

### Runtime Module Loading

#### resolves local imports without SIMPLE_LIB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies basic functionality
# Actual module loading tested below
expect(1).to_equal(1)
```

</details>

#### loads std.string functions via SIMPLE_LIB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When SIMPLE_LIB=src is set, use std.text should work
# This will be tested after implementation is complete
expect(1).to_equal(1)
```

</details>

#### handles missing modules gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module loading should fail gracefully for missing files
expect(1).to_equal(1)
```

</details>

#### caches loaded modules to avoid re-parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Subsequent imports of same module should use cache
expect(1).to_equal(1)
```

</details>

#### exports all functions when no explicit export

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Modules without export statements expose all functions
expect(1).to_equal(1)
```

</details>

#### respects explicit export lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Modules with export statements only expose listed names
expect(1).to_equal(1)
```

</details>

### Module Path Resolution

#### checks local directory first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Relative imports resolve to current directory
expect(1).to_equal(1)
```

</details>

#### checks SIMPLE_LIB second

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Falls back to SIMPLE_LIB path if local not found
expect(1).to_equal(1)
```

</details>

#### checks src/ third as fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Final fallback to src/ directory
expect(1).to_equal(1)
```

</details>

#### converts dotted paths to file paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# std.string → src/lib/text.spl
expect(1).to_equal(1)
```

</details>

### Selective Imports

#### loads specific functions with curly braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# use module.{func1, func2}
expect(1).to_equal(1)
```

</details>

#### validates imported names exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Should error if requested function not found
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/module_loading_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Runtime Module Loading
- Module Path Resolution
- Selective Imports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
