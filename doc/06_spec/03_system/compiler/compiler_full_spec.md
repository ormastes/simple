# Compiler Full Specification

> Tests covering Compiler Full Facade.

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

- interprets a simple program successfully
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interprets a simple program successfully")
val src_path = "/tmp/sml_compiler_full_interpret_ok.spl"
write_file(src_path, simple_program())

val result = interpret_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### checks a valid source file successfully

- checks a valid source file successfully
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks a valid source file successfully")
val src_path = "/tmp/sml_compiler_full_check_ok.spl"
write_file(src_path, simple_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### compile_file writes the default smf artifact

- compile_file writes the default smf artifact
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_file writes the default smf artifact")
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

- compile_to_smf writes the requested artifact path
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_to_smf writes the requested artifact path")
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

- aot_vhdl_file writes the backend artifact file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes the backend artifact file")
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

- aot_c_file writes the backend artifact file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_c_file writes the backend artifact file")
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

- generate_headers emits both c and c++ headers for exported items
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(c_path) is true
   - Expected: rt_file_exists(cpp_path) is true
   - Expected: c_header contains `add`
   - Expected: cpp_header contains `class Pair`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generate_headers emits both c and c++ headers for exported items")
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

- parse_sdn_file returns success for readable data
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_sdn_file returns success for readable data")
val sdn_path = "/tmp/sml_compiler_full_data.sdn"
write_file(sdn_path, "root:" + NL + "  name: \"compiler-full\"")

val result = parse_sdn_file(sdn_path)

expect(result.is_success()).to_equal(true)
delete_file(sdn_path)
```

</details>

#### when reporting bounded failures honestly

#### check_file fails on malformed source with a non-empty error

- check_file fails on malformed source with a non-empty error
   - Expected: result.is_success() is false
   - Expected: result.get_errors().join("\n").len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_file fails on malformed source with a non-empty error")
val src_path = "/tmp/sml_compiler_full_check_fail.spl"
write_file(src_path, invalid_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n").len() > 0).to_equal(true)
delete_file(src_path)
```

</details>

#### compile_to_smf fails on malformed source with a non-empty error

- compile_to_smf fails on malformed source with a non-empty error
   - Expected: result.is_ok() is false
   - Expected: error.len() > 0 is true
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_to_smf fails on malformed source with a non-empty error")
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

- generate_headers rejects files without exported c items
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generate_headers rejects files without exported c items")
val src_path = "/tmp/sml_compiler_full_headers_fail.spl"
write_file(src_path, simple_program())

val result = generate_headers(src_path, "/tmp/sml_compiler_full_headers_fail", "demo", true, false)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("no @export(\"C\") items found")
delete_file(src_path)
```

</details>

#### compile_files rejects unsupported multi-source facade usage

- compile_files rejects unsupported multi-source facade usage
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_files rejects unsupported multi-source facade usage")
val result = compile_files(["a.spl", "b.spl"], CompileMode.Aot)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("only supports a single input path")
```

</details>

#### compile_files rejects smf execution mode in the facade

- compile_files rejects smf execution mode in the facade
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_files rejects smf execution mode in the facade")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Compiler Full Facade.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `439233e15f8a156397e4823dc2bf26be5a4c5798fa410c61b58cb45360db7b10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `439233e15f8a156397e4823dc2bf26be5a4c5798fa410c61b58cb45360db7b10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `439233e15f8a156397e4823dc2bf26be5a4c5798fa410c61b58cb45360db7b10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/compiler_full_spec.spl
mirror: doc/06_spec/03_system/compiler/compiler_full_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/compiler_full_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/compiler_full_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/compiler_full_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interprets a simple program successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_full_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks a valid source file successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_full_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compile_file writes the default smf artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
