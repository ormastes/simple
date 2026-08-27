# CLI Native Build Main Contract Spec

Source: `test/01_unit/app/cli_native_build_main_contract_spec.spl`

## Native build main dispatch contract

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Main Contract Specification

## Scenarios

### native build main dispatch contract

#### keeps the VHDL compiler entry in-process and core-safe

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the VHDL compiler entry in-process and core-safe
   - Expected: source does not contain `aot_vhdl_file`
   - Expected: source does not contain `native-build`
   - Expected: source does not contain `rt_native_build`
   - Expected: source does not contain `rt_process_run`
   - Expected: source does not contain `SIMPLE_RUNTIME_PATH`
   - Expected: source does not contain `libsimple_native_all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the VHDL compiler entry in-process and core-safe")
val source = file_read("src/app/cli/vhdl_compile_entry.spl")

expect(source).to_contain(
    "compiler_driver_create, compiler_driver_run_vhdl")
expect(source).to_contain(
    'rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY", source)')
expect(source).to_contain(
    'rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE", "0")')
expect(source).to_contain(
    "val result = compiler_driver_run_vhdl(compiler_driver_create(options))")
expect(source.contains("aot_vhdl_file")).to_equal(false)
expect(source.contains("native-build")).to_equal(false)
expect(source.contains("rt_native_build")).to_equal(false)
expect(source.contains("rt_process_run")).to_equal(false)
expect(source.contains("SIMPLE_RUNTIME_PATH")).to_equal(false)
expect(source.contains("libsimple_native_all")).to_equal(false)
```

</details>

#### keeps the bounded Gen2 compiler product source-less and explicit

- keeps the bounded Gen2 compiler product source-less and explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the bounded Gen2 compiler product source-less and explicit")
val source = file_read("src/app/cli/vhdl_compile_entry.spl")

expect(source).to_contain("--riscv-gen2-product")
expect(source).to_contain("RISCV_GEN2_ZCA_CONTROL_PREDECODE_PRODUCT")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_control_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_migrating_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv32_cjal_migrating_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv64_addiw_migrating_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv32_cjal_single_outstanding_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv64_addiw_single_outstanding_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_trap_single_outstanding_product")
expect(source).to_contain("RISCV_GEN2_ZCA_MIGRATING_PREDECODE_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV32_CJAL_MIGRATING_PREDECODE_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV64_ADDIW_MIGRATING_PREDECODE_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV32_CJAL_SINGLE_OUTSTANDING_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV64_ADDIW_SINGLE_OUTSTANDING_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_TRAP_SINGLE_OUTSTANDING_PRODUCT")
expect(source).to_contain(
    "(source != \"\" and riscv_gen2_product != \"\")")
expect(source).to_contain("if source != \"\":\n        options.input_files = [source]")
expect(source).to_contain(
    "if riscv_gen2_product != \"\":\n            # A compiler-owned design has no source pathname")
```

</details>

#### keeps the native-build parent worker-only and bounded

- keeps the native-build parent worker-only and bounded
   - Expected: source does not contain `use std.cli.cli_util`
   - Expected: source does not contain `return cli_native_build(args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the native-build parent worker-only and bounded")
val source = file_read("src/app/cli/native_build_main.spl")

expect(source).to_contain("extern fn rt_cli_get_args() -> [text]")
expect(source.contains("use std.cli.cli_util")).to_equal(false)
expect(source).to_contain("fn native_build_text_eq(a: text, b: text) -> bool:")
expect(source).to_contain("run_native_build_worker(args)")
expect(source).to_end_with("    run_native_build_worker(args)\n")
expect(source.contains("return cli_native_build(args)")).to_equal(false)
expect(source).to_contain("return abs_if_needed(from_binary)")
expect(source).to_contain("return abs_if_needed(from_bin)")
expect(source).to_contain("return abs_if_needed(se)")
expect(source).to_contain('process_run_timeout("ps", ["-p",')
expect(source).to_contain('"comm="], 2000)')
expect(source).to_contain("return darwin_out.trim()")
expect(source).to_contain("env_set(\"SIMPLE_BINARY\", simple_bin)")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_WORKER\", \"1\")")
expect(source).to_contain("fn native_build_output_has_nil_field_id(stdout: text, stderr: text) -> bool:")
expect(source).to_contain("native_build_print_failure_hints(stdout, stderr)")
expect(source).to_contain("SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1")
```

This is source-contract evidence only; no rebuilt self-hosted executable was
produced, so it does not verify the native startup repair.
