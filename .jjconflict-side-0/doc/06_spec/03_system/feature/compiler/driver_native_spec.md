# Driver Native

> Tests the native compilation driver including command-line argument parsing, build mode selection, and output file management. Verifies that the driver correctly orchestrates the compilation pipeline from entry point to final binary.

<!-- sdn-diagram:id=driver_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_native_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Native

Tests the native compilation driver including command-line argument parsing, build mode selection, and output file management. Verifies that the driver correctly orchestrates the compilation pipeline from entry point to final binary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/driver_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the native compilation driver including command-line argument parsing, build
mode selection, and output file management. Verifies that the driver correctly
orchestrates the compilation pipeline from entry point to final binary.

## Scenarios

### Driver Native

#### compiles a simple function via driver and exits 0

1. rt file write text
2. output file: Some
3. var driver = CompilerDriver create
   - Expected: run_exit equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val source = "fn main() -> i64:\n    0\n"
    rt_file_write_text("/tmp/driver_native_input.spl", source)
    var options = CompileOptions(
        mode: CompileMode.Aot,
        input_files: ["/tmp/driver_native_input.spl"],
        output_file: Some("/tmp/driver_native_output"),
        output_format: OutputFormat.Native,
        optimize: false,
        opt_level: nil,
        release: false,
        debug_info: false,
        verbose: false,
        log_level: 0,
        profile: "dev",
        no_borrow_check: true,
        backend: "native",
        interpreter_mode: "optimized",
        gc_off: false
    )
    var driver = CompilerDriver.create(options)
    val result = driver.compile()
    var compiled_path = ""
    var run_exit = -1
    match result:
        case Success(path):
            if path != nil:
                compiled_path = path
                val run_r = rt_process_run(compiled_path, [])
                run_exit = run_r[2]
        case _:
            compiled_path = ""
    expect(compiled_path.len()).to_be_greater_than(0)
    expect(run_exit).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
