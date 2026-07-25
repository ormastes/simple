# Llvm Compiled Proof Specification

> <details>

<!-- sdn-diagram:id=llvm_compiled_proof_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_compiled_proof_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_compiled_proof_spec -> std
llvm_compiled_proof_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_compiled_proof_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Compiled Proof Specification

## Scenarios

### LLVM Capability Detection

#### produces a valid capability report

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = detect_llvm_capabilities()
expect(report.host_os != "").to_equal(true)
expect(report.host_arch != "").to_equal(true)
```

</details>

#### detects host OS correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = get_llvm_capabilities()
val valid_os = ["linux", "macos", "windows", "freebsd"]
expect(valid_os.contains(report.host_os)).to_equal(true)
```

</details>

#### caches the capability report

1. reset capability cache
   - Expected: r1.host_os equals `r2.host_os`
   - Expected: r1.host_arch equals `r2.host_arch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_capability_cache()
val r1 = get_llvm_capabilities()
val r2 = get_llvm_capabilities()
# Same report instance (cached)
expect(r1.host_os).to_equal(r2.host_os)
expect(r1.host_arch).to_equal(r2.host_arch)
```

</details>

#### generates readable format_report

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = get_llvm_capabilities()
val text = report.format_report()
expect(text.contains("LLVM Capability Report")).to_equal(true)
expect(text.contains("Host:")).to_equal(true)
expect(text.contains("Tools:")).to_equal(true)
expect(text.contains("Backends:")).to_equal(true)
```

</details>

#### reports preferred backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = get_llvm_capabilities()
val preferred = report.preferred_backend()
# Must be one of the three valid choices
val valid = (preferred == BackendKind.LlvmLib or
             preferred == BackendKind.Llvm or
             preferred == BackendKind.Cranelift)
expect(valid).to_equal(true)
```

</details>

#### generates diagnostic for missing LLVM

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = get_llvm_capabilities()
if report.has_any_llvm():
    # If LLVM is available, diagnostic should be empty
    val diag = report.format_diagnostic()
    expect(diag).to_equal("")
else:
    # If LLVM is missing, diagnostic should contain install instructions
    val diag = report.format_diagnostic()
    expect(diag.contains("Install LLVM")).to_equal(true)
```

</details>

### LLVM Version Compatibility

#### parses standard version string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = parse_llvm_version("18.1.3")
expect(v.major).to_equal(18)
expect(v.minor).to_equal(1)
expect(v.patch).to_equal(3)
```

</details>

#### parses verbose llc --version output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = parse_llvm_version("LLVM version 17.0.6\nOptimized build.\nDefault target: x86_64-linux-gnu")
expect(v.major).to_equal(17)
expect(v.minor).to_equal(0)
expect(v.patch).to_equal(6)
```

</details>

#### parses Ubuntu clang version output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = parse_llvm_version("Ubuntu clang version 18.1.3-1ubuntu1 (++20240220094142+ef68c8aed184-1~exp1~20240220214205.50)")
expect(v.major).to_equal(18)
```

</details>

#### handles empty version string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = parse_llvm_version("")
expect(v.is_known()).to_equal(false)
expect(v.to_text()).to_equal("unknown")
```

</details>

#### classifies supported versions correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v16 = parse_llvm_version("16.0.0")
val v18 = parse_llvm_version("18.1.3")
val v19 = parse_llvm_version("19.0.0")
expect(check_version_compatibility(v16)).to_equal(LlvmVersionStatus.Supported)
expect(check_version_compatibility(v18)).to_equal(LlvmVersionStatus.Supported)
expect(check_version_compatibility(v19)).to_equal(LlvmVersionStatus.Supported)
```

</details>

#### rejects too-old versions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v15 = parse_llvm_version("15.0.0")
val v12 = parse_llvm_version("12.0.0")
expect(check_version_compatibility(v15)).to_equal(LlvmVersionStatus.TooOld)
expect(check_version_compatibility(v12)).to_equal(LlvmVersionStatus.TooOld)
```

</details>

#### warns on too-new versions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v20 = parse_llvm_version("20.0.0")
val v25 = parse_llvm_version("25.0.0")
expect(check_version_compatibility(v20)).to_equal(LlvmVersionStatus.TooNew)
expect(check_version_compatibility(v25)).to_equal(LlvmVersionStatus.TooNew)
```

</details>

#### handles unknown version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vunk = parse_llvm_version("garbage")
expect(check_version_compatibility(vunk)).to_equal(LlvmVersionStatus.Unknown)
```

</details>

### Cross-Target Toolchain Descriptors

#### returns a toolchain for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = toolchain_for_target(CodegenTarget.X86_64)
expect(tc.triple.contains("x86_64")).to_equal(true)
expect(tc.linker != "").to_equal(true)
```

</details>

#### returns a toolchain for aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = toolchain_for_target(CodegenTarget.AArch64)
expect(tc.triple.contains("aarch64")).to_equal(true)
```

</details>

#### returns a toolchain for armv7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = toolchain_for_target(CodegenTarget.Arm)
expect(tc.triple.contains("armv7")).to_equal(true)
```

</details>

#### returns a toolchain for riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = toolchain_for_target(CodegenTarget.Riscv32)
expect(tc.triple.contains("riscv32")).to_equal(true)
```

</details>

#### returns a toolchain for wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = toolchain_for_target(CodegenTarget.Wasm32)
expect(tc.triple.contains("wasm32")).to_equal(true)
expect(tc.linker_flavor).to_equal("wasm-ld")
```

</details>

#### generates diagnostic report for all targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = diagnose_all_targets()
expect(report.contains("Cross-Target Toolchain Status")).to_equal(true)
expect(report.contains("x86_64")).to_equal(true)
expect(report.contains("aarch64")).to_equal(true)
expect(report.contains("wasm32")).to_equal(true)
```

</details>

#### provides install hints for cross targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = toolchain_for_target(CodegenTarget.AArch64)
val caps = get_llvm_capabilities()
if caps.host_arch != "aarch64":
    # Cross-compile scenario
    expect(tc.requires_external).to_equal(true)
    expect(tc.install_hint != "").to_equal(true)
```

</details>

### Hosted Native Compilation Proof

#### llvm-lib compiles for x86_64 when available

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = MirModule(
    name: "llvm_lib_x86_64_compiled_proof",
    functions: [],
    statics: {},
    constants: {},
    types: {}
)
val result = compile_module_with_backend("llvm-lib", module, false)
expect(result.is_ok()).to_equal(true)
val compiled = result.unwrap()
expect(compiled.object_code.len() > 0).to_equal(true)
```

</details>

#### llvm (CLI) compiles for x86_64 when available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val config = LlvmTargetConfig__for_target(CodegenTarget.X86_64, nil)
val result = compile_ir_to_object(trivial_main_ir(), config, OptimizationLevel.Debug)
expect(result.is_ok()).to_equal(true)
val object = result.unwrap()
expect(object.bytes.?).to_equal(true)
expect(object.bytes.unwrap().len() > 0).to_equal(true)
```

</details>

#### llvm CLI links an aarch64 executable when cross toolchain is present

1. file delete
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = shell("command -v aarch64-linux-gnu-gcc 2>/dev/null")
if tc.exit_code != 0:
    val pending_reason = "aarch64-linux-gnu-gcc not available"
    expect(pending_reason.len()).to_be_greater_than(0)

val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
val obj_result = compile_ir_to_object(trivial_main_ir(), config, OptimizationLevel.Debug)
expect(obj_result.is_ok()).to_equal(true)
val object = obj_result.unwrap()
val obj_path = "/tmp/simple_llvm_aarch64_probe.o"
val out_path = "/tmp/simple_llvm_aarch64_probe.out"
expect(write_object_bytes(obj_path, object.bytes)).to_equal(true)

val link = shell("aarch64-linux-gnu-gcc -o {out_path} {obj_path} 2>&1")
expect(link.exit_code).to_equal(0)
expect(file_exists(out_path)).to_equal(true)

file_delete(obj_path)
file_delete(out_path)
```

</details>

#### llvm CLI links a riscv64 executable when cross toolchain is present

1. file delete
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = shell("command -v riscv64-linux-gnu-gcc 2>/dev/null")
if tc.exit_code != 0:
    val pending_reason = "riscv64-linux-gnu-gcc not available"
    expect(pending_reason.len()).to_be_greater_than(0)

val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv64, nil)
val obj_result = compile_ir_to_object(trivial_main_ir(), config, OptimizationLevel.Debug)
expect(obj_result.is_ok()).to_equal(true)
val object = obj_result.unwrap()
val obj_path = "/tmp/simple_llvm_riscv64_probe.o"
val out_path = "/tmp/simple_llvm_riscv64_probe.out"
expect(write_object_bytes(obj_path, object.bytes)).to_equal(true)

val link = shell("riscv64-linux-gnu-gcc -o {out_path} {obj_path} 2>&1")
expect(link.exit_code).to_equal(0)
expect(file_exists(out_path)).to_equal(true)

file_delete(obj_path)
file_delete(out_path)
```

</details>

#### llvm CLI emits a wasm32 artifact when wasm linker is present

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = shell("command -v wasm-ld 2>/dev/null")
if tc.exit_code != 0:
    val pending_reason = "wasm-ld not available"
    expect(pending_reason.len()).to_be_greater_than(0)

val config = LlvmTargetConfig__for_target(CodegenTarget.Wasm32, nil)
val out_path = "/tmp/simple_llvm_wasm32_probe.wasm"
val result = compile_ir_to_wasm(trivial_main_ir(), config, OptimizationLevel.Debug, out_path)
expect(result.is_ok()).to_equal(true)
expect(file_exists(out_path)).to_equal(true)
expect(file_size_raw(out_path)).to_be_greater_than(8)
file_delete(out_path)
```

</details>

#### llvm CLI emits a wasm64 artifact when wasm linker is present

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = shell("command -v wasm-ld 2>/dev/null")
if tc.exit_code != 0:
    val pending_reason = "wasm-ld not available"
    expect(pending_reason.len()).to_be_greater_than(0)

val config = LlvmTargetConfig__for_target(CodegenTarget.Wasm64, nil)
val out_path = "/tmp/simple_llvm_wasm64_probe.wasm"
val result = compile_ir_to_wasm(trivial_main_ir(), config, OptimizationLevel.Debug, out_path)
expect(result.is_ok()).to_equal(true)
expect(file_exists(out_path)).to_equal(true)
expect(file_size_raw(out_path)).to_be_greater_than(8)
file_delete(out_path)
```

</details>

### Support Matrix

#### contains entries for all required targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
expect(matrix.len() > 0).to_equal(true)
# Must have at least 16 entries (8 targets x 2 backends)
expect(matrix.len() >= 16).to_equal(true)
```

</details>

#### x86_64 is stable on both backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_level = lookup_support(BackendKind.LlvmLib, CodegenTarget.X86_64)
val cli_level = lookup_support(BackendKind.Llvm, CodegenTarget.X86_64)
expect(lib_level).to_equal(LlvmSupportLevel.Stable)
expect(cli_level).to_equal(LlvmSupportLevel.Stable)
```

</details>

<details>
<summary>Advanced: matches published support levels for the cross-target matrix</summary>

#### matches published support levels for the cross-target matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# i686: demoted to unsupported (multilib not portable)
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.X86)).to_equal(LlvmSupportLevel.Unsupported)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.X86)).to_equal(LlvmSupportLevel.Unsupported)
# aarch64: both stable (libLLVM includes AArch64 natively)
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.AArch64)).to_equal(LlvmSupportLevel.Stable)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.AArch64)).to_equal(LlvmSupportLevel.Stable)
# armv7: demoted to unsupported (hard-float ABI not portable)
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.Arm)).to_equal(LlvmSupportLevel.Unsupported)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.Arm)).to_equal(LlvmSupportLevel.Unsupported)
# riscv64: both stable (libLLVM includes RISC-V natively)
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv64)).to_equal(LlvmSupportLevel.Stable)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.Riscv64)).to_equal(LlvmSupportLevel.Stable)
# riscv32: demoted to unsupported (baremetal-only, not portable)
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv32)).to_equal(LlvmSupportLevel.Unsupported)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.Riscv32)).to_equal(LlvmSupportLevel.Unsupported)
# wasm: llvm-lib unsupported, CLI stable
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32)).to_equal(LlvmSupportLevel.Unsupported)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32)).to_equal(LlvmSupportLevel.Stable)
expect(lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm64)).to_equal(LlvmSupportLevel.Unsupported)
expect(lookup_support(BackendKind.Llvm, CodegenTarget.Wasm64)).to_equal(LlvmSupportLevel.Stable)
```

</details>


</details>

#### wasm32 is stable on llvm CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32)
expect(level).to_equal(LlvmSupportLevel.Stable)
```

</details>

#### wasm32 is unsupported on llvm-lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32)
expect(level).to_equal(LlvmSupportLevel.Unsupported)
```

</details>

<details>
<summary>Advanced: formats human-readable matrix</summary>

#### formats human-readable matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = format_support_matrix()
expect(text.contains("Support Matrix")).to_equal(true)
expect(text.contains("llvm-lib")).to_equal(true)
expect(text.contains("llvm (CLI)")).to_equal(true)
expect(text.contains("stable")).to_equal(true)
```

</details>


</details>

#### exports SDN format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = export_matrix_sdn()
expect(sdn.contains("matrix {")).to_equal(true)
expect(sdn.contains("backend:")).to_equal(true)
expect(sdn.contains("target:")).to_equal(true)
expect(sdn.contains("level:")).to_equal(true)
```

</details>

### Negative and Diagnostic Cases

#### unsupported version produces TooOld diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = parse_llvm_version("15.0.0")
val status = check_version_compatibility(v)
expect(status).to_equal(LlvmVersionStatus.TooOld)
```

</details>

#### unknown combination returns Unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GPU targets not in LLVM matrix
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.CudaPtx)
expect(level).to_equal(LlvmSupportLevel.Unsupported)
```

</details>

#### capability report includes warnings for known issues

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = get_llvm_capabilities()
# Warnings list exists (may be empty on a well-configured system)
expect(report.warnings != nil).to_equal(true)
```

</details>

#### capability report includes errors for known issues

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = get_llvm_capabilities()
# Errors list exists
expect(report.errors != nil).to_equal(true)
```

</details>

### wasm closure confirmation

#### wasm32 llvm CLI is stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32)
expect(level.to_text()).to_equal("stable")
```

</details>

#### wasm64 llvm CLI is stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### wasm32 llvm-lib is unsupported with clear reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32)
expect(level.to_text()).to_equal("unsupported")
val matrix = get_support_matrix()
for entry in matrix:
    if entry.backend == BackendKind.LlvmLib and entry.target == CodegenTarget.Wasm32:
        expect(entry.known_limits).to_contain("use llvm backend")
```

</details>

#### wasm64 llvm-lib is unsupported with clear reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm64)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### wasm levels are all in final states

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w32_lib = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32)
val w32_cli = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32)
val w64_lib = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm64)
val w64_cli = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm64)
expect(w32_lib.is_final_state()).to_equal(true)
expect(w32_cli.is_final_state()).to_equal(true)
expect(w64_lib.is_final_state()).to_equal(true)
expect(w64_cli.is_final_state()).to_equal(true)
```

</details>

### matrix closure validation

<details>
<summary>Advanced: validate_matrix_closure returns no errors</summary>

#### validate_matrix_closure returns no errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = validate_matrix_closure()
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: is_matrix_closed returns true</summary>

#### is_matrix_closed returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val closed = is_matrix_closed()
expect(closed).to_equal(true)
```

</details>


</details>

#### no row is Partial

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    val level_text = entry.level.to_text()
    expect(level_text != "partial").to_equal(true)
```

</details>

#### no row is SupportedExternal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    val level_text = entry.level.to_text()
    expect(level_text != "supported (external toolchain)").to_equal(true)
```

</details>

#### every row is in a final state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    expect(entry.level.is_final_state()).to_equal(true)
```

</details>

#### stable rows have proof references

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    if entry.level.to_text() == "stable":
        expect(entry.proof != "none").to_equal(true)
        expect(entry.proof != "").to_equal(true)
```

</details>

#### unsupported rows have clear diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = get_support_matrix()
for entry in matrix:
    if entry.level.to_text() == "unsupported":
        expect(entry.known_limits != "").to_equal(true)
```

</details>

### matrix completeness

<details>
<summary>Advanced: matrix covers all 8 targets for llvm-lib</summary>

#### matrix covers all 8 targets for llvm-lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = [
    CodegenTarget.X86_64, CodegenTarget.X86,
    CodegenTarget.AArch64, CodegenTarget.Arm,
    CodegenTarget.Riscv64, CodegenTarget.Riscv32,
    CodegenTarget.Wasm32, CodegenTarget.Wasm64
]
for target in targets:
    val level = lookup_support(BackendKind.LlvmLib, target)
    # Every target must have an entry (not default Unsupported from missing)
    expect(level.is_final_state()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: matrix covers all 8 targets for llvm CLI</summary>

#### matrix covers all 8 targets for llvm CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = [
    CodegenTarget.X86_64, CodegenTarget.X86,
    CodegenTarget.AArch64, CodegenTarget.Arm,
    CodegenTarget.Riscv64, CodegenTarget.Riscv32,
    CodegenTarget.Wasm32, CodegenTarget.Wasm64
]
for target in targets:
    val level = lookup_support(BackendKind.Llvm, target)
    expect(level.is_final_state()).to_equal(true)
```

</details>


</details>

#### closure report says COMPLETE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = format_closure_report()
expect(report).to_contain("COMPLETE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_compiled_proof_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM Capability Detection
- LLVM Version Compatibility
- Cross-Target Toolchain Descriptors
- Hosted Native Compilation Proof
- Support Matrix
- Negative and Diagnostic Cases
- wasm closure confirmation
- matrix closure validation
- matrix completeness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
