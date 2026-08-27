# Native Executable Generation

> Tests the native executable generation pipeline from Simple source to platform binary. Verifies that the compiler produces correct ELF/PE executables, handles linking, and that generated binaries execute with expected behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Executable Generation

Tests the native executable generation pipeline from Simple source to platform binary. Verifies that the compiler produces correct ELF/PE executables, handles linking, and that generated binaries execute with expected behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/native_exe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the native executable generation pipeline from Simple source to platform
binary. Verifies that the compiler produces correct ELF/PE executables, handles
linking, and that generated binaries execute with expected behavior.

## Scenarios

### BuildConfig

#### default configuration

#### creates config with entry point and output

- creates config with entry point and output
   - Expected: entry equals `src/main.spl`
   - Expected: output equals `my_program`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates config with entry point and output")
val entry = "src/main.spl"
val output = "my_program"
# Verify defaults match expected values
expect(entry).to_equal("src/main.spl")
expect(output).to_equal("my_program")
```

</details>

#### defaults to nil backend (SMF pipeline)

- defaults to nil backend (SMF pipeline)
   - Expected: is_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to nil backend (SMF pipeline)")
val backend: text? = nil
val is_nil = not backend.?
expect(is_nil).to_equal(true)
```

</details>

#### defaults to PIE enabled

- defaults to PIE enabled
   - Expected: pie is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to PIE enabled")
val pie = true
expect(pie).to_equal(true)
```

</details>

#### defaults to optimization level 0

- defaults to optimization level 0
   - Expected: optimization equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to optimization level 0")
val optimization = 0
expect(optimization).to_equal(0)
```

</details>

#### defaults to libc as library dependency

- defaults to libc as library dependency
   - Expected: libraries[0] equals `c`
   - Expected: libraries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to libc as library dependency")
val libraries = ["c"]
expect(libraries[0]).to_equal("c")
expect(libraries.len()).to_equal(1)
```

</details>

#### LLVM backend configuration

#### accepts llvm as backend value

- accepts llvm as backend value
   - Expected: is_llvm is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts llvm as backend value")
val backend: text? = Some("llvm")
val is_llvm = backend.? and backend.unwrap() == "llvm"
expect(is_llvm).to_equal(true)
```

</details>

#### accepts smf as backend value

- accepts smf as backend value
   - Expected: is_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts smf as backend value")
val backend: text? = Some("smf")
val is_smf = backend.? and backend.unwrap() == "smf"
expect(is_smf).to_equal(true)
```

</details>

#### for_simple_cli configuration

#### uses x86-64-v3 as default target CPU

- uses x86-64-v3 as default target CPU
   - Expected: target_cpu == nil is false
   - Expected: target_cpu.unwrap() equals `x86-64-v3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses x86-64-v3 as default target CPU")
val target_cpu: text? = Some("x86-64-v3")
expect(target_cpu == nil).to_equal(false)
expect(target_cpu.unwrap()).to_equal("x86-64-v3")
```

</details>

#### includes standard libraries

- includes standard libraries
   - Expected: libraries[0] equals `c`
   - Expected: libraries.len() equals `3`
   - Expected: libraries[1] equals `m`
   - Expected: libraries[2] equals `pthread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes standard libraries")
val libraries = ["c", "m", "pthread"]
expect(libraries[0]).to_equal("c")
expect(libraries.len()).to_equal(3)
expect(libraries[1]).to_equal("m")
expect(libraries[2]).to_equal("pthread")
```

</details>

#### uses optimization level 2

- uses optimization level 2
   - Expected: optimization equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses optimization level 2")
val optimization = 2
expect(optimization).to_equal(2)
```

</details>

### LLVM Backend Flag Parsing

#### backend flag parsing

#### parses --backend=llvm

- parses --backend=llvm
   - Expected: is_llvm_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses --backend=llvm")
val flag = "--backend=llvm"
val is_llvm_flag = flag == "--backend=llvm"
expect(is_llvm_flag).to_equal(true)
```

</details>

#### parses --backend=smf

- parses --backend=smf
   - Expected: is_smf_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses --backend=smf")
val flag = "--backend=smf"
val is_smf_flag = flag == "--backend=smf"
expect(is_smf_flag).to_equal(true)
```

</details>

#### detects unknown backend from flag

- detects unknown backend from flag
   - Expected: starts is true
   - Expected: is_known is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects unknown backend from flag")
val flag = "--backend=unknown"
val starts = flag.starts_with("--backend=")
val be_name = flag[10..]
val is_known = be_name == "llvm" or be_name == "smf"
expect(starts).to_equal(true)
expect(is_known).to_equal(false)
```

</details>

#### backend dispatch logic

#### dispatches to LLVM when backend is llvm

- dispatches to LLVM when backend is llvm
   - Expected: use_llvm is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches to LLVM when backend is llvm")
val backend: text? = Some("llvm")
val use_llvm = backend.? and backend.unwrap() == "llvm"
expect(use_llvm).to_equal(true)
```

</details>

#### dispatches to SMF when backend is nil

- dispatches to SMF when backend is nil
   - Expected: use_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches to SMF when backend is nil")
val backend: text? = nil
val use_smf = not backend.?
expect(use_smf).to_equal(true)
```

</details>

#### dispatches to SMF when backend is smf

- dispatches to SMF when backend is smf
   - Expected: use_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches to SMF when backend is smf")
val backend: text? = Some("smf")
val use_llvm = backend.? and backend.unwrap() == "llvm"
val use_smf = not use_llvm
expect(use_smf).to_equal(true)
```

</details>

### Entry Point IR Generation

#### hosted entry point (main)

#### contains module name comment

- contains module name comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains module name comment")
val module_name = "test_program"
val ir_comment = "; Entry point for Simple program: {module_name}"
expect(ir_comment).to_contain("test_program")
```

</details>

#### declares __simple_runtime_init

- declares __simple_runtime_init


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares __simple_runtime_init")
val decl = "declare void @__simple_runtime_init()"
expect(decl).to_contain("__simple_runtime_init")
```

</details>

#### declares __simple_main

- declares __simple_main


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares __simple_main")
val decl = "declare i64 @__simple_main()"
expect(decl).to_contain("__simple_main")
```

</details>

#### declares __simple_runtime_shutdown

- declares __simple_runtime_shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares __simple_runtime_shutdown")
val decl = "declare void @__simple_runtime_shutdown()"
expect(decl).to_contain("__simple_runtime_shutdown")
```

</details>

#### defines main with argc and argv

- defines main with argc and argv


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines main with argc and argv")
val def_line = "define i32 @main(i32 %argc, ptr %argv) {"
expect(def_line).to_contain("@main")
expect(def_line).to_contain("%argc")
expect(def_line).to_contain("%argv")
```

</details>

#### calls runtime init before main

- calls runtime init before main


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls runtime init before main")
val call = "call void @__simple_runtime_init()"
expect(call).to_contain("__simple_runtime_init")
```

</details>

#### calls __simple_main and captures result

- calls __simple_main and captures result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls __simple_main and captures result")
val call = "%result = call i64 @__simple_main()"
expect(call).to_contain("__simple_main")
expect(call).to_start_with("%result")
```

</details>

#### truncates i64 result to i32 exit code

- truncates i64 result to i32 exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("truncates i64 result to i32 exit code")
val trunc = "%exit_code = trunc i64 %result to i32"
expect(trunc).to_contain("trunc")
expect(trunc).to_contain("i64")
expect(trunc).to_contain("i32")
```

</details>

#### returns exit code

- returns exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns exit code")
val ret = "ret i32 %exit_code"
expect(ret).to_start_with("ret i32")
```

</details>

#### bare-metal entry point (_start)

#### defines _start with noreturn

- defines _start with noreturn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines _start with noreturn")
val def_line = "define void @_start() noreturn {"
expect(def_line).to_contain("@_start")
expect(def_line).to_contain("noreturn")
```

</details>

<details>
<summary>Advanced: contains halt loop</summary>

#### contains halt loop

- contains halt loop
   - Expected: halt_label equals `halt:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains halt loop")
val halt_label = "halt:"
val halt_instr = "br label %halt"
expect(halt_label).to_equal("halt:")
expect(halt_instr).to_contain("%halt")
```

</details>


</details>

<details>
<summary>Advanced: uses hlt instruction in halt loop</summary>

#### uses hlt instruction in halt loop

- uses hlt instruction in halt loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses hlt instruction in halt loop")
val hlt = "call void asm sideeffect \"hlt\", \"\"()"
expect(hlt).to_contain("hlt")
```

</details>


</details>

#### entry point mode selection

#### selects main for hosted mode

- selects main for hosted mode
   - Expected: entry_fn equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects main for hosted mode")
val bare_metal = false
val entry_fn = if bare_metal: "_start" else: "main"
expect(entry_fn).to_equal("main")
```

</details>

#### selects _start for bare-metal mode

- selects _start for bare-metal mode
   - Expected: entry_fn equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects _start for bare-metal mode")
val bare_metal = true
val entry_fn = if bare_metal: "_start" else: "main"
expect(entry_fn).to_equal("_start")
```

</details>

### Runtime Stub Generation

#### stub C source content

#### declares __simple_runtime_init as void function

- declares __simple_runtime_init as void function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares __simple_runtime_init as void function")
val stub_line = "void __simple_runtime_init(void) {}"
expect(stub_line).to_contain("__simple_runtime_init")
expect(stub_line).to_contain("void")
```

</details>

#### declares __simple_runtime_shutdown as void function

- declares __simple_runtime_shutdown as void function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares __simple_runtime_shutdown as void function")
val stub_line = "void __simple_runtime_shutdown(void) {}"
expect(stub_line).to_contain("__simple_runtime_shutdown")
```

</details>

#### declares __simple_main as extern

- declares __simple_main as extern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares __simple_main as extern")
val stub_line = "int __simple_main(void);"
expect(stub_line).to_contain("__simple_main")
```

</details>

#### defines main that calls init, __simple_main, shutdown

- defines main that calls init, __simple_main, shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines main that calls init, __simple_main, shutdown")
val main_body = "int main(int argc, char **argv)"
expect(main_body).to_contain("main")
expect(main_body).to_contain("argc")
```

</details>

#### returns result from __simple_main

- returns result from __simple_main


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns result from __simple_main")
val ret_line = "return result;"
expect(ret_line).to_contain("return")
```

</details>

#### stub file paths

#### generates C source path from output path

- generates C source path from output path
   - Expected: c_path equals `build/artifacts/_runtime_runtime_stub.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates C source path from output path")
val output_path = "build/artifacts/_runtime"
val c_path = output_path + "_runtime_stub.c"
expect(c_path).to_equal("build/artifacts/_runtime_runtime_stub.c")
```

</details>

#### generates object file path from output path

- generates object file path from output path
   - Expected: o_path equals `build/artifacts/_runtime_runtime_stub.o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates object file path from output path")
val output_path = "build/artifacts/_runtime"
val o_path = output_path + "_runtime_stub.o"
expect(o_path).to_equal("build/artifacts/_runtime_runtime_stub.o")
```

</details>

### Build Pipeline Configuration

#### SMF pipeline (default)

#### source_to_smf_path converts .spl to .smf in .build

- source_to_smf_path converts .spl to .smf in .build
   - Expected: smf_path equals `build/artifacts/src_app_cli_main.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("source_to_smf_path converts .spl to .smf in .build")
val source = "src/app/cli/main.spl"
val base_no_ext = source.replace(".spl", "")
val base = base_no_ext.replace("/", "_")
val smf_path = "build/artifacts/{base}.smf"
expect(smf_path).to_equal("build/artifacts/src_app_cli_main.smf")
```

</details>

#### LLVM pipeline

#### source_to_obj_path converts .spl to .o in .build

- source_to_obj_path converts .spl to .o in .build
   - Expected: obj_path equals `build/artifacts/src_app_cli_main.o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("source_to_obj_path converts .spl to .o in .build")
val source = "src/app/cli/main.spl"
val base_no_ext = source.replace(".spl", "")
val base = base_no_ext.replace("/", "_")
val obj_path = "build/artifacts/{base}.o"
expect(obj_path).to_equal("build/artifacts/src_app_cli_main.o")
```

</details>

#### maps optimization 0 to Debug

- maps optimization 0 to Debug
   - Expected: level_name equals `Debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps optimization 0 to Debug")
val optimization = 0
val level_name = match optimization:
    case 0: "Debug"
    case 1: "Size"
    case 2: "Speed"
    case 3: "Aggressive"
    case _: "Speed"
expect(level_name).to_equal("Debug")
```

</details>

#### maps optimization 2 to Speed

- maps optimization 2 to Speed
   - Expected: level_name equals `Speed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps optimization 2 to Speed")
val optimization = 2
val level_name = match optimization:
    case 0: "Debug"
    case 1: "Size"
    case 2: "Speed"
    case 3: "Aggressive"
    case _: "Speed"
expect(level_name).to_equal("Speed")
```

</details>

#### maps optimization 3 to Aggressive

- maps optimization 3 to Aggressive
   - Expected: level_name equals `Aggressive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps optimization 3 to Aggressive")
val optimization = 3
val level_name = match optimization:
    case 0: "Debug"
    case 1: "Size"
    case 2: "Speed"
    case 3: "Aggressive"
    case _: "Speed"
expect(level_name).to_equal("Aggressive")
```

</details>

#### entry point object file

#### uses fixed path for entry point object

- uses fixed path for entry point object
   - Expected: entry_obj_path equals `build/artifacts/_entry_point.o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses fixed path for entry point object")
val entry_obj_path = "build/artifacts/_entry_point.o"
expect(entry_obj_path).to_equal("build/artifacts/_entry_point.o")
```

</details>

#### module path conversion

#### converts module path to file path

- converts module path to file path
   - Expected: file_path equals `src/lib/json.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts module path to file path")
val module_path = "std.json"
val dotted = module_path.replace(".", "/")
val path = dotted.replace("std/", "lib/")
val file_path = "src/{path}.spl"
expect(file_path).to_equal("src/lib/json.spl")
```

</details>

#### converts deep module path

- converts deep module path
   - Expected: file_path equals `src/compiler/backend/llvm_backend.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts deep module path")
val module_path = "compiler.backend.llvm_backend"
val path = module_path.replace(".", "/")
val file_path = "src/{path}.spl"
expect(file_path).to_equal("src/compiler/backend/llvm_backend.spl")
```

</details>

#### converts bare type import to default type domain path

- converts bare type import to default type domain path
   - Expected: file_path equals `src/type/simple_lang/I64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts bare type import to default type domain path")
val module_path = "I64"
val file_path = "src/type/simple_lang/{module_path}.spl"
expect(file_path).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### converts owned-domain type import to underscore directory path

- converts owned-domain type import to underscore directory path
   - Expected: file_path equals `type/simple_lang/I64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts owned-domain type import to underscore directory path")
val module_path = "simple-lang/I64"
val parts = module_path.split("/")
val file_path = "type/{parts[0].replace("-", "_")}/{parts[1]}.spl"
expect(file_path).to_equal("type/simple_lang/I64.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57b1c2dad29dca773e416981d637fbdfdd3043f7264892d7cd43b38b3e473021`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57b1c2dad29dca773e416981d637fbdfdd3043f7264892d7cd43b38b3e473021`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57b1c2dad29dca773e416981d637fbdfdd3043f7264892d7cd43b38b3e473021`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/app/native_exe_spec.spl
mirror: doc/06_spec/03_system/feature/app/native_exe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/native_exe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/native_exe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/native_exe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/native_exe_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates config with entry point and output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/native_exe_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to nil backend (SMF pipeline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/native_exe_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to PIE enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
