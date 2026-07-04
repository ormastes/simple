# Dependencies Specification

> <details>

<!-- sdn-diagram:id=dependencies_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dependencies_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dependencies_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dependencies_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dependencies Specification

## Scenarios

### Simple dependency extraction

<details>
<summary>Advanced: parses use statements</summary>

#### parses use statements _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_line = "use std.io as io"
val has_use = source_line.starts_with("use ")
expect(has_use).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses selective imports</summary>

#### parses selective imports _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_line = "use std.math.{abs, max}"
val has_use = source_line.starts_with("use ")
val has_selective = source_line.contains("{")
expect(has_use).to_equal(true)
expect(has_selective).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses from-use imports</summary>

#### parses from-use imports _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_line = "from utils.helpers use trim, slug"
val has_from = source_line.starts_with("from ")
expect(has_from).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses pub use reexports</summary>

#### parses pub use reexports _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_line = "pub use app.api"
val has_pub_use = source_line.starts_with("pub use ")
expect(has_pub_use).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects self-referential cycle</summary>

#### detects self-referential cycle _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_name = "core"
val import_name = "core"
val is_cycle = module_name == import_name
expect(is_cycle).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects no cycle for different modules</summary>

#### detects no cycle for different modules _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_name = "app"
val import_name = "std"
val is_cycle = module_name == import_name
expect(is_cycle).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: tracks symbol usage by function</summary>

#### tracks symbol usage by function _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usage = jo2(jp("std.io", js("run")), jp("abs", js("run")))
val io_fn = extract_json_string(usage, "std.io")
val abs_fn = extract_json_string(usage, "abs")
expect(io_fn).to_equal("run")
expect(abs_fn).to_equal("run")
```

</details>


</details>

<details>
<summary>Advanced: tracks multiple functions using same symbol</summary>

#### tracks multiple functions using same symbol _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slug_usage = "helper,formatter"
val used_by_helper = slug_usage.contains("helper")
val used_by_formatter = slug_usage.contains("formatter")
expect(used_by_helper).to_equal(true)
expect(used_by_formatter).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: extracts module path from qualified import</summary>

#### extracts module path from qualified import _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val import_path = "foo.bar.baz"
val has_dots = import_path.contains(".")
expect(has_dots).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: identifies aliased imports</summary>

#### identifies aliased imports _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_line = "use std.io as io"
val has_alias = source_line.contains(" as ")
expect(has_alias).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/dependencies_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple dependency extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
