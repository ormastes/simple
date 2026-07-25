# Nvme Fw Rv32 Entry Fail Mask Specification

> <details>

<!-- sdn-diagram:id=nvme_fw_rv32_entry_fail_mask_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_fw_rv32_entry_fail_mask_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_fw_rv32_entry_fail_mask_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_fw_rv32_entry_fail_mask_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Fw Rv32 Entry Fail Mask Specification

## Scenarios

### NVMe rv32 entry fail mask

#### propagates the full selftest failure mask

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl") ?? ""

expect(source).to_contain("val fail = raw_fail")
expect(source).to_not_contain("raw_fail & 65535")
expect(source).to_contain("if (mask & 1048576) != 0:")
expect(source).to_contain("_emit_fail_mask(fail)")
```

</details>

#### aggregates logic subtests as section bit flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic.spl") ?? ""

expect(source).to_contain("fn _nvme_fw_rv32_section_flag(result: i64, bit: i64) -> i64:")
expect(source).to_contain("if result != 0:")
expect(source).to_contain("return bit")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_rain_selftest(), 1)")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_reactor_selftest(), 4096)")
expect(source).to_contain("_nvme_fw_rv32_section_flag(rv32_namespace_guard_selftest(), 1048576)")
expect(source).to_not_contain("fail = fail + rv32_")
```

</details>

#### keeps the build wrapper on the stock rv32 boot-hook path

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs") ?? ""

expect(source).to_contain("$SIMPLE_BIN\" native-build --backend llvm")
expect(source).to_contain("SIMPLE_COMPILER_PHASE_PROFILE=1")
expect(source).to_contain("timeout -k 10s")
expect(source).to_contain("use os.kernel.arch.riscv32.boot")
expect(source).to_contain("use entry.")
expect(source).to_contain("rt_rv32_boot_optional_nvme_fw_selftest")
expect(source).to_contain("--source build/os/generated --source src --source examples/09_embedded/simpleos_nvme_fw/fw_rv32")
expect(source).to_not_contain("fn _start():")
expect(source).to_not_contain("fn _qemu_exit_fail():")
expect(source).to_not_contain("SIMPLE_BOOTSTRAP=1")
expect(source).to_not_contain("--timeout \"$TIMEOUT_SECS\"")
```

</details>

#### keeps compiler phase profiling independent of full compiler trace

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/80.driver/driver_log_helpers.spl") ?? ""

expect(source).to_contain("SIMPLE_COMPILER_PHASE_PROFILE")
expect(source).to_contain("SIMPLE_COMPILER_TRACE")
```

</details>

#### keeps native-build declaration arenas off process-env mirrors

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_source = rt_file_read_text("src/app/io/_CliCompile/compile_targets.spl") ?? ""
val decl_source = rt_file_read_text("src/compiler/10.frontend/core/_Ast/decl_nodes.spl") ?? ""

expect(cli_source).to_contain("SIMPLE_NATIVE_ARENA_DECLS")
expect(cli_source).to_contain("env_set(\"SIMPLE_NATIVE_ARENA_DECLS\", \"1\")")
expect(cli_source).to_contain("env_set(\"SIMPLE_NATIVE_ARENA_DECLS\", old_native_arena_decls)")
expect(decl_source).to_contain("ast_decl_prefer_arena")
```

</details>

#### reuses parsed native entry-closure modules during HIR lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/80.driver/driver.spl") ?? ""

expect(source).to_contain("val entry_module_for_hir = self.ctx.modules[name]")
expect(source).to_contain("lowering.lower_parser_module_unstub(entry_module_for_hir)")
expect(source).to_contain("val reparsed_entry_module = parse_full_frontend")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe rv32 entry fail mask

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
