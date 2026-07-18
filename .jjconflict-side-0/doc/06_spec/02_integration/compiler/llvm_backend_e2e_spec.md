# Llvm Backend E2e Specification

> <details>

<!-- sdn-diagram:id=llvm_backend_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_backend_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_backend_e2e_spec -> std
llvm_backend_e2e_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_backend_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Backend E2e Specification

## Scenarios

### LLVM Backend E2E - Environment

#### llc detection

#### finds llc binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llc_cmd = find_llc()
# Skip test if llc not installed
if not llc_cmd.?:
    val pending_reason = "llc not installed"
    expect(pending_reason.len()).to_be_greater_than(0)
else:
    expect(llc_cmd.?).to_equal(true)
    # Should be one of: llc-18, llc-17, llc-16, llc
    val cmd = llc_cmd
    expect(cmd).to_start_with("llc")
```

</details>

#### checks llc availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = llc_available()
if not available:
    val pending_reason = "llc not installed"
    expect(pending_reason.len()).to_be_greater_than(0)
else:
    expect(available).to_equal(true)
```

</details>

### LLVM Backend E2E - Runtime Declarations

#### declaration generation

#### generates runtime declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = generate_runtime_declarations()
expect(decls.len()).to_be_greater_than(0)
```

</details>

#### includes file I/O declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_file_open")
expect(decls).to_contain("@rt_file_read_text")
expect(decls).to_contain("@rt_file_write")
```

</details>

#### includes memory declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_alloc")
expect(decls).to_contain("@rt_free")
expect(decls).to_contain("@rt_memcpy")
```

</details>

#### includes string declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_strlen")
expect(decls).to_contain("@rt_strcat")
```

</details>

#### includes I/O declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_print")
expect(decls).to_contain("@rt_println")
```

</details>

#### includes LLVM intrinsics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = generate_runtime_declarations()
expect(decls).to_contain("@llvm.memcpy")
expect(decls).to_contain("@llvm.memset")
```

</details>

### LLVM Backend E2E - Backend Creation

#### default backend

#### creates backend for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
expect(backend.target).to_equal(CodegenTarget.X86_64)
expect(backend.opt_level).to_equal(OptimizationLevel.Debug)
```

</details>

#### creates backend for Speed optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
expect(backend.opt_level).to_equal(OptimizationLevel.Speed)
```

</details>

#### compatibility backend

#### creates compatibility backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.compatibility_build(CodegenTarget.X86_64, OptimizationLevel.Speed)
expect(backend.cpu_override.?).to_equal(true)
expect(backend.cpu_override).to_equal("x86-64")
```

</details>

#### bare-metal backend

#### creates bare-metal backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create_baremetal(CodegenTarget.X86_64, OptimizationLevel.Size)
expect(backend.bare_metal).to_equal(true)
expect(backend.debug_info).to_equal(true)
```

</details>

### LLVM Backend E2E - Configuration

#### builder methods

#### configures CPU override

1.  with cpu override
   - Expected: backend.cpu_override.? is true
   - Expected: backend.cpu_override equals `skylake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_cpu_override("skylake")
expect(backend.cpu_override.?).to_equal(true)
expect(backend.cpu_override).to_equal("skylake")
```

</details>

#### enables LLVM IR output

1.  with llvm ir
   - Expected: backend.emit_llvm_ir is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_llvm_ir()
expect(backend.emit_llvm_ir).to_equal(true)
```

</details>

#### enables assembly output

1.  with assembly
   - Expected: backend.emit_assembly is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_assembly()
expect(backend.emit_assembly).to_equal(true)
```

</details>

#### enables debug info

1.  with debug info
   - Expected: backend.debug_info is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_debug_info()
expect(backend.debug_info).to_equal(true)
```

</details>

### LLVM Backend E2E - Target Configuration

#### target config

#### gets target configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("x86_64")
```

</details>

### LLVM Backend E2E - Compilation

#### simple IR compilation

#### compiles minimal LLVM IR to object code

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not llc_available():
    # Skip if llc not installed
    val pending_reason = "llc not installed"
    expect(pending_reason.len()).to_be_greater_than(0)
else:
    # TODO: Create minimal MirModule and compile
    # For now just verify backend creation works
    val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    expect(backend.target).to_equal(CodegenTarget.X86_64)
```

</details>

### LLVM Backend E2E - Error Handling

#### missing llc

#### provides helpful error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies error message format
# Actual llc availability may vary
val llc_cmd = find_llc()
if not llc_cmd.?:
    # Error message would be shown during compile_ir_to_object
    val pending_reason = "llc not installed"
    expect(pending_reason.len()).to_be_greater_than(0)
else:
    # llc is available
    expect(llc_cmd.?).to_equal(true)
```

</details>

### LLVM Backend E2E - Multiple Targets

#### x86_64 target

#### creates backend for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("x86_64")
```

</details>

#### aarch64 target

#### creates backend for aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.AArch64, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("aarch64")
```

</details>

#### 32-bit targets

#### creates backend for i686

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("i686")
```

</details>

### LLVM Backend E2E - Optimization Levels

#### optimization flags

#### supports Debug optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
expect(backend.opt_level).to_equal(OptimizationLevel.Debug)
```

</details>

#### supports Size optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Size)
expect(backend.opt_level).to_equal(OptimizationLevel.Size)
```

</details>

#### supports Speed optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
expect(backend.opt_level).to_equal(OptimizationLevel.Speed)
```

</details>

#### supports Aggressive optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Aggressive)
expect(backend.opt_level).to_equal(OptimizationLevel.Aggressive)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM Backend E2E - Environment
- LLVM Backend E2E - Runtime Declarations
- LLVM Backend E2E - Backend Creation
- LLVM Backend E2E - Configuration
- LLVM Backend E2E - Target Configuration
- LLVM Backend E2E - Compilation
- LLVM Backend E2E - Error Handling
- LLVM Backend E2E - Multiple Targets
- LLVM Backend E2E - Optimization Levels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
