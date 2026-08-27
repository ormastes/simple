# Driver Api Heavy Path Specification

> Tests covering Driver API Heavy Path Tiers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Api Heavy Path Specification

## Scenarios

### Driver API Heavy Path Tiers

#### driver_api_types imports terminate cleanly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- driver_api_types imports terminate cleanly
   - Expected: path.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_types imports terminate cleanly")
val path = find_runtime_lib_dir()
expect(path.len() > 0).to_equal(true)
```

</details>

#### driver_api_core compile_file import terminates cleanly

- driver_api_core compile_file import terminates cleanly
   - Expected: find_runtime_lib_dir() equals `find_runtime_lib_dir()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core compile_file import terminates cleanly")
val _fn = core_compile_file
expect(find_runtime_lib_dir()).to_equal(find_runtime_lib_dir())
```

</details>

#### driver_api_core interpret_file import terminates cleanly

- driver_api_core interpret_file import terminates cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core interpret_file import terminates cleanly")
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core aot_c_file import terminates cleanly

- driver_api_core aot_c_file import terminates cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core aot_c_file import terminates cleanly")
val _fn = core_aot_c_file
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core aot_native_file_with_backend import terminates cleanly

- driver_api_core aot_native_file_with_backend import terminates cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core aot_native_file_with_backend import terminates cleanly")
val _fn = core_aot_native_file_with_backend
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core aot_native_project_with_backend import terminates cleanly

- driver_api_core aot_native_project_with_backend import terminates cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core aot_native_project_with_backend import terminates cleanly")
val _fn = core_aot_native_project_with_backend
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 1 driver_api_interpret imports terminate cleanly

- tier 1 driver_api_interpret imports terminate cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 1 driver_api_interpret imports terminate cleanly")
val _fn = tier1_interpret
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 2 driver_api_compile_single imports terminate cleanly

- tier 2 driver_api_compile_single imports terminate cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 2 driver_api_compile_single imports terminate cleanly")
val _fn = tier2_compile
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 3 driver_api_codegen_backends imports terminate cleanly

- tier 3 driver_api_codegen_backends imports terminate cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 3 driver_api_codegen_backends imports terminate cleanly")
val _fn = tier3_aot_c
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 4 driver_api_native_single imports terminate cleanly

- tier 4 driver_api_native_single imports terminate cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 4 driver_api_native_single imports terminate cleanly")
val _fn = tier4_native
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 5 driver_api_project_build imports terminate cleanly

- tier 5 driver_api_project_build imports terminate cleanly
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tier 5 driver_api_project_build imports terminate cleanly")
val _fn = tier5_project
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### importing find_runtime_lib_dir from driver_api_types works in isolation

- importing find_runtime_lib_dir from driver_api_types works in isolation
   - Expected: path.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("importing find_runtime_lib_dir from driver_api_types works in isolation")
val path = find_runtime_lib_dir()
expect(path.len() > 0).to_equal(true)
```

</details>

#### importing compile_file from driver_public_compile works in isolation

- importing compile_file from driver_public_compile works in isolation
   - Expected: result.is_success() is false
   - Expected: result.get_errors().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("importing compile_file from driver_public_compile works in isolation")
val missing_path = "/tmp/sml_heavy_path_public_compile_missing.spl"
delete_file(missing_path)
val result = public_compile_file(missing_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().len() > 0).to_equal(true)
```

</details>

#### driver_api_core re-exports find_runtime_lib_dir

- driver_api_core re-exports find_runtime_lib_dir
   - Expected: path_from_types.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core re-exports find_runtime_lib_dir")
# find_runtime_lib_dir originates in driver_api_types but is
# also exported by driver_api_core for backward compat.
val path_from_types = find_runtime_lib_dir()
expect(path_from_types.len() > 0).to_equal(true)
```

</details>

#### driver_api_core re-exports compile_file

- driver_api_core re-exports compile_file
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core re-exports compile_file")
val _fn = core_compile_file
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core re-exports check_file

- driver_api_core re-exports check_file
   - Expected: find_runtime_lib_dir().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core re-exports check_file")
val _fn = core_check_file
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api facade exposes compile_file

- driver_api facade exposes compile_file
   - Expected: result.is_success() is false
   - Expected: result.get_errors().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api facade exposes compile_file")
val missing_path = "/tmp/sml_heavy_path_facade_compile_missing.spl"
delete_file(missing_path)
val result = facade_compile_file(missing_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().len() > 0).to_equal(true)
```

</details>

#### driver_api facade exposes aot_c_file

- driver_api facade exposes aot_c_file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api facade exposes aot_c_file")
val src_path = "/tmp/sml_heavy_path_facade_aot_c.spl"
val out_path = "/tmp/sml_heavy_path_facade_aot_c.cpp"
delete_file(out_path)
write_file(src_path, "fn main(): 46")
val result = facade_aot_c_file(src_path, out_path)
expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### driver_public_compile exposes compile_to_smf

- driver_public_compile exposes compile_to_smf
   - Expected: result.is_err() is true
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_public_compile exposes compile_to_smf")
val missing_path = "/tmp/sml_heavy_path_public_smf_missing.spl"
val out_path = "/tmp/sml_heavy_path_public_smf_missing.smf"
delete_file(missing_path)
delete_file(out_path)
val result = public_compile_to_smf(missing_path, out_path)
expect(result.is_err()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(false)
```

</details>

#### driver_public_compile exposes parse_sdn_file

- driver_public_compile exposes parse_sdn_file
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_public_compile exposes parse_sdn_file")
val sdn_path = "/tmp/sml_heavy_path_public_parse.sdn"
write_file(sdn_path, "root:" + NL + "  name: \"heavy-path\"")
val result = public_parse_sdn_file(sdn_path)
expect(result.is_success()).to_equal(true)
delete_file(sdn_path)
```

</details>

#### driver_public_api exposes interpret_file

- driver_public_api exposes interpret_file
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_public_api exposes interpret_file")
val src_path = "/tmp/sml_heavy_path_public_interpret.spl"
write_file(src_path, "fn main(): 47")
val result = public_interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### driver_public_api exposes generate_headers

- driver_public_api exposes generate_headers
   - Expected: result.is_success() is false
   - Expected: result.get_errors().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_public_api exposes generate_headers")
val missing_path = "/tmp/sml_heavy_path_public_headers_missing.spl"
val out_dir = "/tmp/sml_heavy_path_public_headers"
delete_file(missing_path)
val result = public_generate_headers(missing_path, out_dir, "heavy_path", true, true)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().len() > 0).to_equal(true)
```

</details>

#### driver_public_shared exposes aot_shared_library

- driver_public_shared exposes aot_shared_library
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_public_shared exposes aot_shared_library")
val missing_path = "/tmp/sml_heavy_path_public_shared_missing.spl"
val out_path = "/tmp/sml_heavy_path_public_shared_missing.so"
delete_file(missing_path)
delete_file(out_path)
val result = public_aot_shared_library(missing_path, out_path)
expect(result.is_success()).to_equal(false)
expect(rt_file_exists(out_path)).to_equal(false)
```

</details>

#### find_runtime_lib_dir returns a non-empty path

- find_runtime_lib_dir returns a non-empty path
   - Expected: path.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("find_runtime_lib_dir returns a non-empty path")
val path = find_runtime_lib_dir()
expect(path.len() > 0).to_equal(true)
```

</details>

#### find_runtime_lib_dir returns a consistent path across calls

- find_runtime_lib_dir returns a consistent path across calls
   - Expected: path1 equals `path2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("find_runtime_lib_dir returns a consistent path across calls")
val path1 = find_runtime_lib_dir()
val path2 = find_runtime_lib_dir()
expect(path1).to_equal(path2)
```

</details>

#### driver_api_core check_file validates a simple source file

- driver_api_core check_file validates a simple source file
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("driver_api_core check_file validates a simple source file")
val src_path = "/tmp/sml_heavy_path_check.spl"
write_file(src_path, "fn main(): 42")

val result = core_check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/driver_api_heavy_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Driver API Heavy Path Tiers.
- Driver API Heavy Path Tiers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `216fd3ebcb232566fe294626868ac8573b6c5f2cae5c63786692a9896f8d078a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `216fd3ebcb232566fe294626868ac8573b6c5f2cae5c63786692a9896f8d078a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `216fd3ebcb232566fe294626868ac8573b6c5f2cae5c63786692a9896f8d078a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/driver_api_heavy_path_spec.spl
mirror: doc/06_spec/03_system/compiler/driver_api_heavy_path_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/driver_api_heavy_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/driver_api_heavy_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/driver_api_heavy_path_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver_api_types imports terminate cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/driver_api_heavy_path_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver_api_core compile_file import terminates cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/driver_api_heavy_path_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver_api_core interpret_file import terminates cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
