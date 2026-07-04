# Jit Ffi Specification

> <details>

<!-- sdn-diagram:id=jit_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Ffi Specification

## Scenarios

### JIT SFFI Wrapper

### JitBackend enum

#### defines backend variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = JitBackend.Default
val cranelift = JitBackend.Cranelift
val llvm = JitBackend.LLVM
val unknown = JitBackend.Unknown
```

</details>

#### converts backend to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_to_string(JitBackend.Default)).to_equal("auto")
expect(backend_to_string(JitBackend.Cranelift)).to_equal("cranelift")
expect(backend_to_string(JitBackend.LLVM)).to_equal("llvm")
expect(backend_to_string(JitBackend.Unknown)).to_equal("unknown")
```

</details>

#### converts string to backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_to_backend("auto")).to_equal(JitBackend.Default)
expect(string_to_backend("cranelift")).to_equal(JitBackend.Cranelift)
expect(string_to_backend("llvm")).to_equal(JitBackend.LLVM)
expect(string_to_backend("invalid")).to_equal(JitBackend.Unknown)
```

</details>

### jit_set_backend

#### sets global backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jit_set_backend(JitBackend.Cranelift)
```

</details>

#### accepts all backend types

1. jit set backend
2. jit set backend
3. jit set backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
jit_set_backend(JitBackend.Default)
jit_set_backend(JitBackend.Cranelift)
jit_set_backend(JitBackend.LLVM)
```

</details>

### jit_get_backend

#### returns current backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = jit_get_backend()
```

</details>

### exec_manager_new

#### creates execution manager with default backend

1. exec manager destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = exec_manager_new()
expect(mgr.handle).to_equal(0)
expect(mgr.is_valid).to_equal(false)
expect(mgr.opt_level).to_equal(2)
exec_manager_destroy(mgr)
```

</details>

#### initializes with default optimization

1. exec manager destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = exec_manager_new()
expect(mgr.opt_level).to_equal(2)
exec_manager_destroy(mgr)
```

</details>

### exec_manager_with_backend

#### creates manager with Cranelift

1. exec manager destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = exec_manager_with_backend(JitBackend.Cranelift)
expect(mgr.is_valid).to_equal(false)
exec_manager_destroy(mgr)
```

</details>

#### creates manager with LLVM

1. exec manager destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = exec_manager_with_backend(JitBackend.LLVM)
expect(mgr.is_valid).to_equal(false)
exec_manager_destroy(mgr)
```

</details>

#### creates manager with Default backend

1. exec manager destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = exec_manager_with_backend(JitBackend.Default)
expect(mgr.is_valid).to_equal(false)
exec_manager_destroy(mgr)
```

</details>

### exec_manager_destroy

#### destroys invalid manager safely

1. exec manager destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
exec_manager_destroy(mgr)
```

</details>

### exec_manager_is_valid

#### returns false for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val valid = exec_manager_is_valid(mgr)
expect(valid).to_equal(false)
```

</details>

### CompileStatus

#### has result and error_message fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = CompileStatus(result: CompileResult.Success, error_message: "")
expect(status.error_message).to_equal("")
```

</details>

#### represents success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = CompileStatus(result: CompileResult.Success, error_message: "")
expect(status.result).to_equal(CompileResult.Success)
```

</details>

#### represents error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = CompileStatus(result: CompileResult.Error, error_message: "syntax error")
expect(status.result).to_equal(CompileResult.Error)
expect(status.error_message).to_equal("syntax error")
```

</details>

### exec_manager_compile_source

#### returns error for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val status = exec_manager_compile_source(mgr, "fn add(x, y): x + y")
expect(status.result).to_equal(CompileResult.Error)
expect(status.error_message).to_equal("Invalid execution manager")
```

</details>

### ExecutionResult

#### has success, return_value, and error_message fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ExecutionResult(success: true, return_value: 42, error_message: "")
expect(result.success).to_equal(true)
expect(result.return_value).to_equal(42)
expect(result.error_message).to_equal("")
```

</details>

### exec_manager_call

#### returns error for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val result = exec_manager_call(mgr, "add", [1, 2])
expect(result.success).to_equal(false)
expect(result.error_message).to_equal("Invalid execution manager")
```

</details>

### exec_manager_has_function

#### returns false for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val has = exec_manager_has_function(mgr, "add")
expect(has).to_equal(false)
```

</details>

### exec_manager_list_functions

#### returns empty array for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val funcs = exec_manager_list_functions(mgr)
expect(funcs.len()).to_equal(0)
```

</details>

### exec_manager_backend

#### returns Unknown for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val backend = exec_manager_backend(mgr)
expect(backend).to_equal(JitBackend.Unknown)
```

</details>

### exec_manager_set_opt_level

#### returns false for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val result = exec_manager_set_opt_level(mgr, 3)
expect(result).to_equal(false)
```

</details>

### exec_manager_get_opt_level

#### returns -1 for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val level = exec_manager_get_opt_level(mgr)
expect(level).to_equal(-1)
```

</details>

### exec_manager_last_error

#### returns error for invalid manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
val error = exec_manager_last_error(mgr)
expect(error).to_equal("Invalid execution manager")
```

</details>

### exec_manager_clear_error

#### handles invalid manager safely

1. exec manager clear error


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ExecManager(handle: 0, backend: JitBackend.Default, is_valid: false, opt_level: 2)
exec_manager_clear_error(mgr)
```

</details>

### jit_eval

#### compiles and executes expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jit_eval("21 + 21")
```

</details>

#### returns ExecutionResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jit_eval("42")
val _ = result.success
val _ = result.return_value
val _ = result.error_message
```

</details>

### jit_compile_and_run

#### compiles source and runs function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn add(x, y): x + y"
val result = jit_compile_and_run(source, "add", [10, 32])
```

</details>

#### returns ExecutionResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn square(x): x * x"
val result = jit_compile_and_run(source, "square", [7])
val _ = result.success
```

</details>

### jit_load_and_run

#### loads file and runs function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jit_load_and_run("nonexistent.spl", "main", [])
```

</details>

#### returns ExecutionResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jit_load_and_run("test.spl", "main", [])
val _ = result.success
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/jit_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JIT SFFI Wrapper
- JitBackend enum
- jit_set_backend
- jit_get_backend
- exec_manager_new
- exec_manager_with_backend
- exec_manager_destroy
- exec_manager_is_valid
- CompileStatus
- exec_manager_compile_source
- ExecutionResult
- exec_manager_call
- exec_manager_has_function
- exec_manager_list_functions
- exec_manager_backend
- exec_manager_set_opt_level
- exec_manager_get_opt_level
- exec_manager_last_error
- exec_manager_clear_error
- jit_eval
- jit_compile_and_run
- jit_load_and_run

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
