# App Io Mod Source Run Specification

> 1. fixture = fixture + "fn main

<!-- sdn-diagram:id=app_io_mod_source_run_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_io_mod_source_run_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_io_mod_source_run_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_io_mod_source_run_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Io Mod Source Run Specification

## Scenarios

### app.io.mod source-run compatibility

#### supports direct source-run imports for low-level helpers

1. fixture = fixture + "fn main
2. fixture = fixture + "    val here = cwd
3. fixture = fixture + "    val
   - Expected: file_write("/tmp/app_io_mod_source_run_fixture.spl", fixture) is true
   - Expected: result.exit_code equals `0`
   - Expected: result.stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple = simple_binary()
val quote = "\""
var fixture = "use app.io.mod.{cwd, shell_tuple}\n\n"
fixture = fixture + "fn main():\n"
fixture = fixture + "    val here = cwd()\n"
fixture = fixture + "    val (out, err, code) = shell_tuple({quote}printf ok{quote})\n"
fixture = fixture + "    print here\n"
fixture = fixture + "    print out\n"
expect(file_write("/tmp/app_io_mod_source_run_fixture.spl", fixture)).to_equal(true)

val result = shell(simple + " run /tmp/app_io_mod_source_run_fixture.spl")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("/home/ormastes/dev/pub/simple")
expect(result.stdout).to_contain("ok")
expect(result.stderr).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/app_io_mod_source_run_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.io.mod source-run compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
