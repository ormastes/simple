# Compiler Full Specification

> 1. write file

<!-- sdn-diagram:id=compiler_full_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_full_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_full_spec -> std
compiler_full_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_full_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Full Specification

## Scenarios

### Compiler Full Facade

#### when executing end-to-end success paths

#### interprets a simple program successfully

1. write file
   - Expected: result.is_success() is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_interpret_ok.spl"
write_file(src_path, simple_program())

val result = interpret_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### checks a valid source file successfully

1. write file
   - Expected: result.is_success() is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_check_ok.spl"
write_file(src_path, simple_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### compile_file writes the default smf artifact

1. delete file
2. write file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_compile_default.spl"
val out_path = "/tmp/sml_compiler_full_compile_default.smf"
delete_file(out_path)
write_file(src_path, simple_program())

val result = compile_file(src_path)

expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### compile_to_smf writes the requested artifact path

1. delete file
2. write file
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_compile_custom.spl"
val out_path = "/tmp/sml_compiler_full_compile_custom.smf"
delete_file(out_path)
write_file(src_path, simple_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes the backend artifact file

1. delete file
2. write file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_aot_vhdl.spl"
val out_path = "/tmp/sml_compiler_full_aot_vhdl.vhd"
delete_file(out_path)
write_file(src_path, "fn add(a: i32, b: i32) -> i32:" + NL + "    a + b")

val result = aot_vhdl_file(src_path, out_path)

expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_c_file writes the backend artifact file

1. delete file
2. write file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true
   - Expected: content equals ``
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_aot_c.spl"
val out_path = "/tmp/sml_compiler_full_aot_c.cpp"
delete_file(out_path)
write_file(src_path, "fn main(): 9")

val result = aot_c_file(src_path, out_path)

expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
val content = rt_file_read_text(out_path)
expect(content).to_equal("")
delete_file(src_path)
delete_file(out_path)
```

</details>

#### generate_headers emits both c and c++ headers for exported items

1. delete file
2. delete file
3. write file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(c_path) is true
   - Expected: rt_file_exists(cpp_path) is true
   - Expected: c_header contains `add`
   - Expected: cpp_header contains `class Pair`
4. delete file
5. delete file
6. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_headers.spl"
val out_dir = "/tmp/sml_compiler_full_headers_out"
val c_path = "/tmp/sml_compiler_full_headers_out/demo.h"
val cpp_path = "/tmp/sml_compiler_full_headers_out/demo.hpp"
delete_file(c_path)
delete_file(cpp_path)
write_file(src_path, exported_program())

val result = generate_headers(src_path, out_dir, "demo", true, true)

expect(result.is_success()).to_equal(true)
expect(rt_file_exists(c_path)).to_equal(true)
expect(rt_file_exists(cpp_path)).to_equal(true)
val c_header = rt_file_read_text(c_path)
val cpp_header = rt_file_read_text(cpp_path)
expect(c_header.contains("add")).to_equal(true)
expect(cpp_header.contains("class Pair")).to_equal(true)
delete_file(src_path)
delete_file(c_path)
delete_file(cpp_path)
```

</details>

#### parse_sdn_file returns success for readable data

1. write file
   - Expected: result.is_success() is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_path = "/tmp/sml_compiler_full_data.sdn"
write_file(sdn_path, "root:" + NL + "  name: \"compiler-full\"")

val result = parse_sdn_file(sdn_path)

expect(result.is_success()).to_equal(true)
delete_file(sdn_path)
```

</details>

#### when reporting bounded failures honestly

#### check_file fails on malformed source with a non-empty error

1. write file
   - Expected: result.is_success() is false
   - Expected: result.get_errors().join("\n").len() > 0 is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_check_fail.spl"
write_file(src_path, invalid_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n").len() > 0).to_equal(true)
delete_file(src_path)
```

</details>

#### compile_to_smf fails on malformed source with a non-empty error

1. delete file
2. write file
   - Expected: result.is_ok() is false
   - Expected: error.len() > 0 is true
   - Expected: rt_file_exists(out_path) is false
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_compile_fail.spl"
val out_path = "/tmp/sml_compiler_full_compile_fail.smf"
delete_file(out_path)
write_file(src_path, invalid_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(false)
val error = result.unwrap_err()
expect(error.len() > 0).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(false)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### generate_headers rejects files without exported c items

1. write file
   - Expected: result.is_success() is false
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_compiler_full_headers_fail.spl"
write_file(src_path, simple_program())

val result = generate_headers(src_path, "/tmp/sml_compiler_full_headers_fail", "demo", true, false)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("no @export(\"C\") items found")
delete_file(src_path)
```

</details>

#### compile_files rejects unsupported multi-source facade usage

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compile_files(["a.spl", "b.spl"], CompileMode.Aot)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("only supports a single input path")
```

</details>

#### compile_files rejects smf execution mode in the facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compile_files(["program.spl"], CompileMode.SmfExec)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("SmfExec mode is not supported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_full_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Compiler Full Facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
