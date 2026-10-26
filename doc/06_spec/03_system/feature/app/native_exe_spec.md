# Native Executable Generation

> Tests the native executable generation pipeline from Simple source to platform binary. Verifies that the compiler produces correct ELF/PE executables, handles linking, and that generated binaries execute with expected behavior.

<!-- sdn-diagram:id=native_exe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_exe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_exe_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_exe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the native executable generation pipeline from Simple source to platform
binary. Verifies that the compiler produces correct ELF/PE executables, handles
linking, and that generated binaries execute with expected behavior.

## Scenarios

### BuildConfig

#### default configuration

#### creates config with entry point and output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = "src/main.spl"
val output = "my_program"
# Verify defaults match expected values
expect(entry).to_equal("src/main.spl")
expect(output).to_equal("my_program")
```

</details>

#### defaults to nil backend (SMF pipeline)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text? = nil
val is_nil = not backend.?
expect(is_nil).to_equal(true)
```

</details>

#### defaults to PIE enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pie = true
expect(pie).to_equal(true)
```

</details>

#### defaults to optimization level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optimization = 0
expect(optimization).to_equal(0)
```

</details>

#### defaults to libc as library dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libraries = ["c"]
expect(libraries[0]).to_equal("c")
expect(libraries.len()).to_equal(1)
```

</details>

#### LLVM backend configuration

#### accepts llvm as backend value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text? = Some("llvm")
val is_llvm = backend.? and backend.unwrap() == "llvm"
expect(is_llvm).to_equal(true)
```

</details>

#### accepts smf as backend value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text? = Some("smf")
val is_smf = backend.? and backend.unwrap() == "smf"
expect(is_smf).to_equal(true)
```

</details>

#### for_simple_cli configuration

#### uses x86-64-v3 as default target CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target_cpu: text? = Some("x86-64-v3")
expect(target_cpu.?).to_equal(true)
expect(target_cpu.unwrap()).to_equal("x86-64-v3")
```

</details>

#### includes standard libraries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libraries = ["c", "m", "pthread"]
expect(libraries[0]).to_equal("c")
expect(libraries.len()).to_equal(3)
expect(libraries[1]).to_equal("m")
expect(libraries[2]).to_equal("pthread")
```

</details>

#### uses optimization level 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optimization = 2
expect(optimization).to_equal(2)
```

</details>

### LLVM Backend Flag Parsing

#### backend flag parsing

#### parses --backend=llvm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--backend=llvm"
val is_llvm_flag = flag == "--backend=llvm"
expect(is_llvm_flag).to_equal(true)
```

</details>

#### parses --backend=smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--backend=smf"
val is_smf_flag = flag == "--backend=smf"
expect(is_smf_flag).to_equal(true)
```

</details>

#### detects unknown backend from flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text? = Some("llvm")
val use_llvm = backend.? and backend.unwrap() == "llvm"
expect(use_llvm).to_equal(true)
```

</details>

#### dispatches to SMF when backend is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text? = nil
val use_smf = not backend.?
expect(use_smf).to_equal(true)
```

</details>

#### dispatches to SMF when backend is smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text? = Some("smf")
val use_llvm = backend.? and backend.unwrap() == "llvm"
val use_smf = not use_llvm
expect(use_smf).to_equal(true)
```

</details>

### Entry Point IR Generation

#### hosted entry point (main)

#### contains module name comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_name = "test_program"
val ir_comment = "; Entry point for Simple program: {module_name}"
expect(ir_comment).to_contain("test_program")
```

</details>

#### declares __simple_runtime_init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = "declare void @__simple_runtime_init()"
expect(decl).to_contain("__simple_runtime_init")
```

</details>

#### declares __simple_main

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = "declare i64 @__simple_main()"
expect(decl).to_contain("__simple_main")
```

</details>

#### declares __simple_runtime_shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = "declare void @__simple_runtime_shutdown()"
expect(decl).to_contain("__simple_runtime_shutdown")
```

</details>

#### defines main with argc and argv

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val def_line = "define i32 @main(i32 %argc, ptr %argv) {"
expect(def_line).to_contain("@main")
expect(def_line).to_contain("%argc")
expect(def_line).to_contain("%argv")
```

</details>

#### calls runtime init before main

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call = "call void @__simple_runtime_init()"
expect(call).to_contain("__simple_runtime_init")
```

</details>

#### calls __simple_main and captures result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val call = "%result = call i64 @__simple_main()"
expect(call).to_contain("__simple_main")
expect(call).to_start_with("%result")
```

</details>

#### truncates i64 result to i32 exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trunc = "%exit_code = trunc i64 %result to i32"
expect(trunc).to_contain("trunc")
expect(trunc).to_contain("i64")
expect(trunc).to_contain("i32")
```

</details>

#### returns exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret = "ret i32 %exit_code"
expect(ret).to_start_with("ret i32")
```

</details>

#### bare-metal entry point (_start)

#### defines _start with noreturn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val def_line = "define void @_start() noreturn {"
expect(def_line).to_contain("@_start")
expect(def_line).to_contain("noreturn")
```

</details>

<details>
<summary>Advanced: contains halt loop</summary>

#### contains halt loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hlt = "call void asm sideeffect \"hlt\", \"\"()"
expect(hlt).to_contain("hlt")
```

</details>


</details>

#### entry point mode selection

#### selects main for hosted mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bare_metal = false
val entry_fn = if bare_metal: "_start" else: "main"
expect(entry_fn).to_equal("main")
```

</details>

#### selects _start for bare-metal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bare_metal = true
val entry_fn = if bare_metal: "_start" else: "main"
expect(entry_fn).to_equal("_start")
```

</details>

### Runtime Stub Generation

#### stub C source content

#### declares __simple_runtime_init as void function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub_line = "void __simple_runtime_init(void) {}"
expect(stub_line).to_contain("__simple_runtime_init")
expect(stub_line).to_contain("void")
```

</details>

#### declares __simple_runtime_shutdown as void function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub_line = "void __simple_runtime_shutdown(void) {}"
expect(stub_line).to_contain("__simple_runtime_shutdown")
```

</details>

#### declares __simple_main as extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub_line = "int __simple_main(void);"
expect(stub_line).to_contain("__simple_main")
```

</details>

#### defines main that calls init, __simple_main, shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val main_body = "int main(int argc, char **argv)"
expect(main_body).to_contain("main")
expect(main_body).to_contain("argc")
```

</details>

#### returns result from __simple_main

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_line = "return result;"
expect(ret_line).to_contain("return")
```

</details>

#### stub file paths

#### generates C source path from output path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_path = "build/artifacts/_runtime"
val c_path = output_path + "_runtime_stub.c"
expect(c_path).to_equal("build/artifacts/_runtime_runtime_stub.c")
```

</details>

#### generates object file path from output path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_path = "build/artifacts/_runtime"
val o_path = output_path + "_runtime_stub.o"
expect(o_path).to_equal("build/artifacts/_runtime_runtime_stub.o")
```

</details>

### Build Pipeline Configuration

#### SMF pipeline (default)

#### source_to_smf_path converts .spl to .smf in .build

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "src/app/cli/main.spl"
val base_no_ext = source.replace(".spl", "")
val base = base_no_ext.replace("/", "_")
val smf_path = "build/artifacts/{base}.smf"
expect(smf_path).to_equal("build/artifacts/src_app_cli_main.smf")
```

</details>

#### LLVM pipeline

#### source_to_obj_path converts .spl to .o in .build

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "src/app/cli/main.spl"
val base_no_ext = source.replace(".spl", "")
val base = base_no_ext.replace("/", "_")
val obj_path = "build/artifacts/{base}.o"
expect(obj_path).to_equal("build/artifacts/src_app_cli_main.o")
```

</details>

#### maps optimization 0 to Debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry_obj_path = "build/artifacts/_entry_point.o"
expect(entry_obj_path).to_equal("build/artifacts/_entry_point.o")
```

</details>

#### module path conversion

#### converts module path to file path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "std.json"
val dotted = module_path.replace(".", "/")
val path = dotted.replace("std/", "lib/")
val file_path = "src/{path}.spl"
expect(file_path).to_equal("src/lib/json.spl")
```

</details>

#### converts deep module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "compiler.backend.llvm_backend"
val path = module_path.replace(".", "/")
val file_path = "src/{path}.spl"
expect(file_path).to_equal("src/compiler/backend/llvm_backend.spl")
```

</details>

#### converts bare type import to default type domain path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "I64"
val file_path = "src/type/simple_lang/{module_path}.spl"
expect(file_path).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### converts owned-domain type import to underscore directory path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
