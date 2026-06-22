# Shell Tools Specification

> <details>

<!-- sdn-diagram:id=shell_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_tools_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Tools Specification

## Scenarios

### shell toolchain manifest paths

#### maps clang commands to clang metadata instead of llvm metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clang = _toolchain_manifest_paths("clang")
expect(clang.0).to_equal("/SYS/CLANGVER.TXT")
expect(clang.1).to_equal("/SYS/CLANGMAN.TXT")
expect(clang.2).to_equal("/usr/bin/clang")

val clang20 = _toolchain_manifest_paths("clang-20")
expect(clang20.0).to_equal("/SYS/CLANGVER.TXT")
expect(clang20.1).to_equal("/SYS/CLANGMAN.TXT")
expect(clang20.2).to_equal("/usr/bin/clang-20")
```

</details>

### shell date command production boundary

#### fails explicitly instead of returning a fake epoch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/os/apps/shell/shell_tools_part2.spl")

expect(source.index_of("1970-01-01") ?? -1).to_equal(-1)
expect(source.index_of("no RTC available") ?? -1).to_equal(-1)
expect(source).to_contain("date: realtime clock unavailable")
expect(source).to_contain("fn tool_date(terminal: Terminal) -> i32:\n    \"\"\"Show current date/time.\"\"\"\n    _write_error(terminal, \"date: realtime clock unavailable\")\n    return 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/shell/shell_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shell toolchain manifest paths
- shell date command production boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
