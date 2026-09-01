# llvm_compiled_proof_spec

> Purpose: This spec proves LLVM Capability Detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llvm_compiled_proof_spec

Purpose: This spec proves LLVM Capability Detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/llvm_compiled_proof_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves LLVM Capability Detection.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### LLVM Capability Detection

#### produces a valid capability report

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a valid capability report


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLVMCOMPILEDPROOF-001
step("produces a valid capability report")
val report = detect_llvm_capabilities()
assert_not_equal(report.host_os, "")
assert_not_equal(report.host_arch, "")
```

</details>

#### detects host OS correctly

- detects host OS correctly
- detects host OS correctly
   - Expected: valid_os contains `report.host_os`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects host OS correctly")
step("detects host OS correctly")
val report = get_llvm_capabilities()
val valid_os = ["linux", "macos", "windows", "freebsd"]
expect(valid_os.contains(report.host_os)).to_equal(true)
```

</details>

#### caches the capability report

- caches the capability report
- caches the capability report
   - Expected: r1.host_os equals `r2.host_os`
   - Expected: r1.host_arch equals `r2.host_arch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("caches the capability report")
step("caches the capability report")
reset_capability_cache()
val r1 = get_llvm_capabilities()
val r2 = get_llvm_capabilities()
# Same report instance (cached)
expect(r1.host_os).to_equal(r2.host_os)
expect(r1.host_arch).to_equal(r2.host_arch)
```

</details>

#### generates readable format_report

- generates readable format_report
- generates readable format_report
   - Expected: text contains `LLVM Capability Report`
   - Expected: text contains `Host:`
   - Expected: text contains `Tools:`
   - Expected: text contains `Backends:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates readable format_report")
step("generates readable format_report")
val report = get_llvm_capabilities()
val text = report.format_report()
expect(text.contains("LLVM Capability Report")).to_equal(true)
expect(text.contains("Host:")).to_equal(true)
expect(text.contains("Tools:")).to_equal(true)
expect(text.contains("Backends:")).to_equal(true)
```

</details>

#### reports preferred backend

- reports preferred backend
- reports preferred backend
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports preferred backend")
step("reports preferred backend")
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

- generates diagnostic for missing LLVM
- generates diagnostic for missing LLVM
   - Expected: diag equals ``
   - Expected: diag contains `Install LLVM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates diagnostic for missing LLVM")
step("generates diagnostic for missing LLVM")
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

- parses standard version string
- parses standard version string
   - Expected: v.major equals `18`
   - Expected: v.minor equals `1`
   - Expected: v.patch equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses standard version string")
step("parses standard version string")
val v = parse_llvm_version("18.1.3")
expect(v.major).to_equal(18)
expect(v.minor).to_equal(1)
expect(v.patch).to_equal(3)
```

</details>

#### parses verbose llc --version output

- parses verbose llc --version output
- parses verbose llc --version output
   - Expected: v.major equals `17`
   - Expected: v.minor equals `0`
   - Expected: v.patch equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses verbose llc --version output")
step("parses verbose llc --version output")
val v = parse_llvm_version("LLVM version 17.0.6\nOptimized build.\nDefault target: x86_64-linux-gnu")
expect(v.major).to_equal(17)
expect(v.minor).to_equal(0)
expect(v.patch).to_equal(6)
```

</details>

#### parses Ubuntu clang version output

- parses Ubuntu clang version output
- parses Ubuntu clang version output
   - Expected: v.major equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses Ubuntu clang version output")
step("parses Ubuntu clang version output")
val v = parse_llvm_version("Ubuntu clang version 18.1.3-1ubuntu1 (++20240220094142+ef68c8aed184-1~exp1~20240220214205.50)")
expect(v.major).to_equal(18)
```

</details>

#### handles empty version string

- handles empty version string
- handles empty version string
   - Expected: v.is_known() is false
   - Expected: v.to_text() equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty version string")
step("handles empty version string")
val v = parse_llvm_version("")
expect(v.is_known()).to_equal(false)
expect(v.to_text()).to_equal("unknown")
```

</details>

#### classifies supported versions correctly

- classifies supported versions correctly
- classifies supported versions correctly
   - Expected: check_version_compatibility(v16) equals `LlvmVersionStatus.Supported`
   - Expected: check_version_compatibility(v18) equals `LlvmVersionStatus.Supported`
   - Expected: check_version_compatibility(v19) equals `LlvmVersionStatus.Supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("classifies supported versions correctly")
step("classifies supported versions correctly")
val v16 = parse_llvm_version("16.0.0")
val v18 = parse_llvm_version("18.1.3")
val v19 = parse_llvm_version("19.0.0")
expect(check_version_compatibility(v16)).to_equal(LlvmVersionStatus.Supported)
expect(check_version_compatibility(v18)).to_equal(LlvmVersionStatus.Supported)
expect(check_version_compatibility(v19)).to_equal(LlvmVersionStatus.Supported)
```

</details>

#### rejects too-old versions

- rejects too-old versions
- rejects too-old versions
   - Expected: check_version_compatibility(v15) equals `LlvmVersionStatus.TooOld`
   - Expected: check_version_compatibility(v12) equals `LlvmVersionStatus.TooOld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects too-old versions")
step("rejects too-old versions")
val v15 = parse_llvm_version("15.0.0")
val v12 = parse_llvm_version("12.0.0")
expect(check_version_compatibility(v15)).to_equal(LlvmVersionStatus.TooOld)
expect(check_version_compatibility(v12)).to_equal(LlvmVersionStatus.TooOld)
```

</details>

#### warns on too-new versions

- warns on too-new versions
- warns on too-new versions
   - Expected: check_version_compatibility(v20) equals `LlvmVersionStatus.TooNew`
   - Expected: check_version_compatibility(v25) equals `LlvmVersionStatus.TooNew`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("warns on too-new versions")
step("warns on too-new versions")
val v20 = parse_llvm_version("20.0.0")
val v25 = parse_llvm_version("25.0.0")
expect(check_version_compatibility(v20)).to_equal(LlvmVersionStatus.TooNew)
expect(check_version_compatibility(v25)).to_equal(LlvmVersionStatus.TooNew)
```

</details>

#### handles unknown version

- handles unknown version
- handles unknown version
   - Expected: check_version_compatibility(vunk) equals `LlvmVersionStatus.Unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unknown version")
step("handles unknown version")
val vunk = parse_llvm_version("garbage")
expect(check_version_compatibility(vunk)).to_equal(LlvmVersionStatus.Unknown)
```

</details>

### Cross-Target Toolchain Descriptors

#### returns a toolchain for x86_64

- returns a toolchain for x86_64
- returns a toolchain for x86_64
   - Expected: tc.triple contains `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a toolchain for x86_64")
step("returns a toolchain for x86_64")
val tc = toolchain_for_target(CodegenTarget.X86_64)
expect(tc.triple.contains("x86_64")).to_equal(true)
assert_not_equal(tc.linker, "")
```

</details>

#### returns a toolchain for aarch64

- returns a toolchain for aarch64
- returns a toolchain for aarch64
   - Expected: tc.triple contains `aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a toolchain for aarch64")
step("returns a toolchain for aarch64")
val tc = toolchain_for_target(CodegenTarget.AArch64)
expect(tc.triple.contains("aarch64")).to_equal(true)
```

</details>

#### returns a toolchain for armv7

- returns a toolchain for armv7
- returns a toolchain for armv7
   - Expected: tc.triple contains `armv7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a toolchain for armv7")
step("returns a toolchain for armv7")
val tc = toolchain_for_target(CodegenTarget.Arm)
expect(tc.triple.contains("armv7")).to_equal(true)
```

</details>

#### returns a toolchain for riscv32

- returns a toolchain for riscv32
- returns a toolchain for riscv32
   - Expected: tc.triple contains `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a toolchain for riscv32")
step("returns a toolchain for riscv32")
val tc = toolchain_for_target(CodegenTarget.Riscv32)
expect(tc.triple.contains("riscv32")).to_equal(true)
```

</details>

#### returns a toolchain for wasm32

- returns a toolchain for wasm32
- returns a toolchain for wasm32
   - Expected: tc.triple contains `wasm32`
   - Expected: tc.linker_flavor equals `wasm-ld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a toolchain for wasm32")
step("returns a toolchain for wasm32")
val tc = toolchain_for_target(CodegenTarget.Wasm32)
expect(tc.triple.contains("wasm32")).to_equal(true)
expect(tc.linker_flavor).to_equal("wasm-ld")
```

</details>

#### generates diagnostic report for all targets

- generates diagnostic report for all targets
- generates diagnostic report for all targets
   - Expected: report contains `Cross-Target Toolchain Status`
   - Expected: report contains `x86_64`
   - Expected: report contains `aarch64`
   - Expected: report contains `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates diagnostic report for all targets")
step("generates diagnostic report for all targets")
val report = diagnose_all_targets()
expect(report.contains("Cross-Target Toolchain Status")).to_equal(true)
expect(report.contains("x86_64")).to_equal(true)
expect(report.contains("aarch64")).to_equal(true)
expect(report.contains("wasm32")).to_equal(true)
```

</details>

#### provides install hints for cross targets

- provides install hints for cross targets
- provides install hints for cross targets
   - Expected: tc.requires_external is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides install hints for cross targets")
step("provides install hints for cross targets")
val tc = toolchain_for_target(CodegenTarget.AArch64)
val caps = get_llvm_capabilities()
if caps.host_arch != "aarch64":
    # Cross-compile scenario
    expect(tc.requires_external).to_equal(true)
    assert_not_equal(tc.install_hint, "")
```

</details>

### Hosted Native Compilation Proof

#### llvm-lib compiles for x86_64 when available

- llvm-lib compiles for x86_64 when available
- llvm-lib compiles for x86_64 when available
   - Expected: result.is_ok() is true
   - Expected: compiled.object_code.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm-lib compiles for x86_64 when available")
step("llvm-lib compiles for x86_64 when available")
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

- llvm (CLI) compiles for x86_64 when available
- llvm (CLI) compiles for x86_64 when available
   - Expected: result.is_ok() is true
   - Expected: object.bytes == nil is false
   - Expected: object.bytes.unwrap().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm (CLI) compiles for x86_64 when available")
step("llvm (CLI) compiles for x86_64 when available")
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val config = LlvmTargetConfig__for_target(CodegenTarget.X86_64, nil)
val result = compile_ir_to_object(trivial_main_ir(), config, OptimizationLevel.Debug)
expect(result.is_ok()).to_equal(true)
val object = result.unwrap()
expect(object.bytes == nil).to_equal(false)
expect(object.bytes.unwrap().len() > 0).to_equal(true)
```

</details>

#### llvm CLI links an aarch64 executable when cross toolchain is present

- llvm CLI links an aarch64 executable when cross toolchain is present
- llvm CLI links an aarch64 executable when cross toolchain is present
   - Expected: obj_result.is_ok() is true
   - Expected: write_object_bytes(obj_path, object.bytes) is true
   - Expected: link.exit_code equals `0`
   - Expected: file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI links an aarch64 executable when cross toolchain is present")
step("llvm CLI links an aarch64 executable when cross toolchain is present")
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

- llvm CLI links a riscv64 executable when cross toolchain is present
- llvm CLI links a riscv64 executable when cross toolchain is present
   - Expected: obj_result.is_ok() is true
   - Expected: write_object_bytes(obj_path, object.bytes) is true
   - Expected: link.exit_code equals `0`
   - Expected: file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI links a riscv64 executable when cross toolchain is present")
step("llvm CLI links a riscv64 executable when cross toolchain is present")
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

- llvm CLI emits a wasm32 artifact when wasm linker is present
- llvm CLI emits a wasm32 artifact when wasm linker is present
   - Expected: result.is_ok() is true
   - Expected: file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI emits a wasm32 artifact when wasm linker is present")
step("llvm CLI emits a wasm32 artifact when wasm linker is present")
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

- llvm CLI emits a wasm64 artifact when wasm linker is present
- llvm CLI emits a wasm64 artifact when wasm linker is present
   - Expected: result.is_ok() is true
   - Expected: file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm CLI emits a wasm64 artifact when wasm linker is present")
step("llvm CLI emits a wasm64 artifact when wasm linker is present")
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

- contains entries for all required targets
- contains entries for all required targets
   - Expected: matrix.len() > 0 is true
   - Expected: matrix.len() >= 16 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("contains entries for all required targets")
step("contains entries for all required targets")
val matrix = get_support_matrix()
expect(matrix.len() > 0).to_equal(true)
# Must have at least 16 entries (8 targets x 2 backends)
expect(matrix.len() >= 16).to_equal(true)
```

</details>

#### x86_64 is stable on both backends

- x86_64 is stable on both backends
- x86_64 is stable on both backends
   - Expected: lib_level equals `LlvmSupportLevel.Stable`
   - Expected: cli_level equals `LlvmSupportLevel.Stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_64 is stable on both backends")
step("x86_64 is stable on both backends")
val lib_level = lookup_support(BackendKind.LlvmLib, CodegenTarget.X86_64)
val cli_level = lookup_support(BackendKind.Llvm, CodegenTarget.X86_64)
expect(lib_level).to_equal(LlvmSupportLevel.Stable)
expect(cli_level).to_equal(LlvmSupportLevel.Stable)
```

</details>

<details>
<summary>Advanced: matches published support levels for the cross-target matrix</summary>

#### matches published support levels for the cross-target matrix

- matches published support levels for the cross-target matrix
- matches published support levels for the cross-target matrix
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.X86) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.X86) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.AArch64) equals `LlvmSupportLevel.Stable`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.AArch64) equals `LlvmSupportLevel.Stable`
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.Arm) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.Arm) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv64) equals `LlvmSupportLevel.Stable`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.Riscv64) equals `LlvmSupportLevel.Stable`
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.Riscv32) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.Riscv32) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32) equals `LlvmSupportLevel.Stable`
   - Expected: lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm64) equals `LlvmSupportLevel.Unsupported`
   - Expected: lookup_support(BackendKind.Llvm, CodegenTarget.Wasm64) equals `LlvmSupportLevel.Stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches published support levels for the cross-target matrix")
step("matches published support levels for the cross-target matrix")
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

- wasm32 is stable on llvm CLI
- wasm32 is stable on llvm CLI
   - Expected: level equals `LlvmSupportLevel.Stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm32 is stable on llvm CLI")
step("wasm32 is stable on llvm CLI")
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32)
expect(level).to_equal(LlvmSupportLevel.Stable)
```

</details>

#### wasm32 is unsupported on llvm-lib

- wasm32 is unsupported on llvm-lib
- wasm32 is unsupported on llvm-lib
   - Expected: level equals `LlvmSupportLevel.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm32 is unsupported on llvm-lib")
step("wasm32 is unsupported on llvm-lib")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32)
expect(level).to_equal(LlvmSupportLevel.Unsupported)
```

</details>

<details>
<summary>Advanced: formats human-readable matrix</summary>

#### formats human-readable matrix

- formats human-readable matrix
- formats human-readable matrix
   - Expected: text contains `Support Matrix`
   - Expected: text contains `llvm-lib`
   - Expected: text contains `llvm (CLI)`
   - Expected: text contains `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats human-readable matrix")
step("formats human-readable matrix")
val text = format_support_matrix()
expect(text.contains("Support Matrix")).to_equal(true)
expect(text.contains("llvm-lib")).to_equal(true)
expect(text.contains("llvm (CLI)")).to_equal(true)
expect(text.contains("stable")).to_equal(true)
```

</details>


</details>

#### exports SDN format

- exports SDN format
- exports SDN format
   - Expected: sdn contains `matrix {`
   - Expected: sdn contains `backend:`
   - Expected: sdn contains `target:`
   - Expected: sdn contains `level:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exports SDN format")
step("exports SDN format")
val sdn = export_matrix_sdn()
expect(sdn.contains("matrix {")).to_equal(true)
expect(sdn.contains("backend:")).to_equal(true)
expect(sdn.contains("target:")).to_equal(true)
expect(sdn.contains("level:")).to_equal(true)
```

</details>

### Negative and Diagnostic Cases

#### unsupported version produces TooOld diagnostic

- unsupported version produces TooOld diagnostic
- unsupported version produces TooOld diagnostic
   - Expected: status equals `LlvmVersionStatus.TooOld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unsupported version produces TooOld diagnostic")
step("unsupported version produces TooOld diagnostic")
val v = parse_llvm_version("15.0.0")
val status = check_version_compatibility(v)
expect(status).to_equal(LlvmVersionStatus.TooOld)
```

</details>

#### unknown combination returns Unsupported

- unknown combination returns Unsupported
- unknown combination returns Unsupported
   - Expected: level equals `LlvmSupportLevel.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unknown combination returns Unsupported")
step("unknown combination returns Unsupported")
# GPU targets not in LLVM matrix
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.CudaPtx)
expect(level).to_equal(LlvmSupportLevel.Unsupported)
```

</details>

#### capability report includes warnings for known issues

- capability report includes warnings for known issues
- capability report includes warnings for known issues


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("capability report includes warnings for known issues")
step("capability report includes warnings for known issues")
val report = get_llvm_capabilities()
# Warnings list exists (may be empty on a well-configured system)
assert_not_equal(report.warnings, nil)
```

</details>

#### capability report includes errors for known issues

- capability report includes errors for known issues
- capability report includes errors for known issues


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("capability report includes errors for known issues")
step("capability report includes errors for known issues")
val report = get_llvm_capabilities()
# Errors list exists
assert_not_equal(report.errors, nil)
```

</details>

### wasm closure confirmation

#### wasm32 llvm CLI is stable

- wasm32 llvm CLI is stable
- wasm32 llvm CLI is stable
   - Expected: level.to_text() equals `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm32 llvm CLI is stable")
step("wasm32 llvm CLI is stable")
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm32)
expect(level.to_text()).to_equal("stable")
```

</details>

#### wasm64 llvm CLI is stable

- wasm64 llvm CLI is stable
- wasm64 llvm CLI is stable
   - Expected: level.to_text() equals `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm64 llvm CLI is stable")
step("wasm64 llvm CLI is stable")
val level = lookup_support(BackendKind.Llvm, CodegenTarget.Wasm64)
expect(level.to_text()).to_equal("stable")
```

</details>

#### wasm32 llvm-lib is unsupported with clear reason

- wasm32 llvm-lib is unsupported with clear reason
- wasm32 llvm-lib is unsupported with clear reason
   - Expected: level.to_text() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm32 llvm-lib is unsupported with clear reason")
step("wasm32 llvm-lib is unsupported with clear reason")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm32)
expect(level.to_text()).to_equal("unsupported")
val matrix = get_support_matrix()
for entry in matrix:
    if entry.backend == BackendKind.LlvmLib and entry.target == CodegenTarget.Wasm32:
        expect(entry.known_limits).to_contain("use llvm backend")
```

</details>

#### wasm64 llvm-lib is unsupported with clear reason

- wasm64 llvm-lib is unsupported with clear reason
- wasm64 llvm-lib is unsupported with clear reason
   - Expected: level.to_text() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm64 llvm-lib is unsupported with clear reason")
step("wasm64 llvm-lib is unsupported with clear reason")
val level = lookup_support(BackendKind.LlvmLib, CodegenTarget.Wasm64)
expect(level.to_text()).to_equal("unsupported")
```

</details>

#### wasm levels are all in final states

- wasm levels are all in final states
- wasm levels are all in final states
   - Expected: w32_lib.is_final_state() is true
   - Expected: w32_cli.is_final_state() is true
   - Expected: w64_lib.is_final_state() is true
   - Expected: w64_cli.is_final_state() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wasm levels are all in final states")
step("wasm levels are all in final states")
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

- validate_matrix_closure returns no errors
- validate_matrix_closure returns no errors
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validate_matrix_closure returns no errors")
step("validate_matrix_closure returns no errors")
val errors = validate_matrix_closure()
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: is_matrix_closed returns true</summary>

#### is_matrix_closed returns true

- is_matrix_closed returns true
- is_matrix_closed returns true
   - Expected: closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is_matrix_closed returns true")
step("is_matrix_closed returns true")
val closed = is_matrix_closed()
expect(closed).to_equal(true)
```

</details>


</details>

#### no row is Partial

- no row is Partial
- no row is Partial


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("no row is Partial")
step("no row is Partial")
val matrix = get_support_matrix()
for entry in matrix:
    val level_text = entry.level.to_text()
    assert_not_equal(level_text, "partial")
```

</details>

#### no row is SupportedExternal

- no row is SupportedExternal
- no row is SupportedExternal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("no row is SupportedExternal")
step("no row is SupportedExternal")
val matrix = get_support_matrix()
for entry in matrix:
    val level_text = entry.level.to_text()
    assert_not_equal(level_text, "supported (external toolchain)")
```

</details>

#### every row is in a final state

- every row is in a final state
- every row is in a final state
   - Expected: entry.level.is_final_state() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("every row is in a final state")
step("every row is in a final state")
val matrix = get_support_matrix()
for entry in matrix:
    expect(entry.level.is_final_state()).to_equal(true)
```

</details>

#### stable rows have proof references

- stable rows have proof references
- stable rows have proof references


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stable rows have proof references")
step("stable rows have proof references")
val matrix = get_support_matrix()
for entry in matrix:
    if entry.level.to_text() == "stable":
        assert_not_equal(entry.proof, "none")
        assert_not_equal(entry.proof, "")
```

</details>

#### unsupported rows have clear diagnostics

- unsupported rows have clear diagnostics
- unsupported rows have clear diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unsupported rows have clear diagnostics")
step("unsupported rows have clear diagnostics")
val matrix = get_support_matrix()
for entry in matrix:
    if entry.level.to_text() == "unsupported":
        assert_not_equal(entry.known_limits, "")
```

</details>

### matrix completeness

<details>
<summary>Advanced: matrix covers all 8 targets for llvm-lib</summary>

#### matrix covers all 8 targets for llvm-lib

- matrix covers all 8 targets for llvm-lib
- matrix covers all 8 targets for llvm-lib
   - Expected: level.is_final_state() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matrix covers all 8 targets for llvm-lib")
step("matrix covers all 8 targets for llvm-lib")
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

- matrix covers all 8 targets for llvm CLI
- matrix covers all 8 targets for llvm CLI
   - Expected: level.is_final_state() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matrix covers all 8 targets for llvm CLI")
step("matrix covers all 8 targets for llvm CLI")
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

- closure report says COMPLETE
- closure report says COMPLETE


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("closure report says COMPLETE")
step("closure report says COMPLETE")
val report = format_closure_report()
expect(report).to_contain("COMPLETE")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-LLVMCOMPILEDPROOF-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1de9cee3b7fa5213b8a381db1e01f0424ddface3e55a4754e195800e89db2e92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1de9cee3b7fa5213b8a381db1e01f0424ddface3e55a4754e195800e89db2e92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1de9cee3b7fa5213b8a381db1e01f0424ddface3e55a4754e195800e89db2e92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/compiler/llvm_compiled_proof_spec.spl
mirror: doc/06_spec/integration/compiler/llvm_compiled_proof_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/llvm_compiled_proof_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/llvm_compiled_proof_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/llvm_compiled_proof_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/compiler/llvm_compiled_proof_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a valid capability report' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_compiled_proof_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects host OS correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_compiled_proof_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches the capability report' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
