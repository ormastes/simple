# Vhdl Backend Cli Smoke Specification

> 1. delete if exists

<!-- sdn-diagram:id=vhdl_backend_cli_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_backend_cli_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_backend_cli_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_backend_cli_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Backend Cli Smoke Specification

## Scenarios

### VHDL backend CLI smoke

#### bin/simple compile --backend=vhdl writes the requested .vhd output

1. delete if exists
2. delete if exists
3. write source
   - Expected: code equals `0`
   - Expected: rt_file_exists(out_path) is true
   - Expected: output.len() > 0 is true
4. delete if exists
5. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/simple_vhdl_cli_explicit.spl"
val out_path = "/tmp/simple_vhdl_cli_explicit.vhd"
delete_if_exists(src_path)
delete_if_exists(out_path)
write_source(src_path, "add")

val (_stdout, _stderr, code) = rt_process_run("bin/simple", ["compile", "--backend=vhdl", src_path, "-o", out_path])

expect(code).to_equal(0)
expect(rt_file_exists(out_path)).to_equal(true)
val output = rt_file_read_text(out_path)
expect(output.len() > 0).to_equal(true)
expect(output).to_contain("entity add is")
expect(output).to_contain("tmp_4 <= a + b;")
expect(output).to_contain("result_out <= tmp_4;")

delete_if_exists(src_path)
delete_if_exists(out_path)
```

</details>

#### bin/simple compile --backend=vhdl writes the default .vhd output

1. delete if exists
2. delete if exists
3. write source
   - Expected: code equals `0`
   - Expected: rt_file_exists(out_path) is true
   - Expected: output.len() > 0 is true
4. delete if exists
5. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/simple_vhdl_cli_default.spl"
val out_path = "/tmp/simple_vhdl_cli_default.vhd"
delete_if_exists(src_path)
delete_if_exists(out_path)
write_source(src_path, "merge")

val (_stdout, _stderr, code) = rt_process_run("bin/simple", ["compile", "--backend=vhdl", src_path])

expect(code).to_equal(0)
expect(rt_file_exists(out_path)).to_equal(true)
val output = rt_file_read_text(out_path)
expect(output.len() > 0).to_equal(true)
expect(output).to_contain("entity merge is")
expect(output).to_contain("tmp_4 <= a + b;")
expect(output).to_contain("result_out <= tmp_4;")

delete_if_exists(src_path)
delete_if_exists(out_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VHDL backend CLI smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
