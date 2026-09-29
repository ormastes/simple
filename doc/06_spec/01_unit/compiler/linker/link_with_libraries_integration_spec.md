# link_with_libraries_integration_spec

> Library linking integration specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# link_with_libraries_integration_spec

Library linking integration specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Library linking integration specification tests.

## Scenarios

### Link With Libraries Integration

#### discovers libraries created on disk

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers libraries created on disk
   - Expected: builder.add_module_data("test/module", [1, 2, 3, 4]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: result.is_ok() is true
   - Expected: libraries.len() equals `1`
   - Expected: libraries[0].name equals `sample`
   - Expected: libraries[0].modules contains `test/module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("discovers libraries created on disk")
val lib_dir = "/tmp/unit_link_with_libraries_scan"
val lib_path = "{lib_dir}/sample.lsm"
_ = shell("mkdir -p '{lib_dir}'")
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data("test/module", [1, 2, 3, 4]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val result = scan_libraries([lib_dir], false)
expect(result.is_ok()).to_equal(true)
val libraries = result.unwrap()
expect(libraries.len()).to_equal(1)
expect(libraries[0].name).to_equal("sample")
expect(libraries[0].modules.contains("test/module")).to_equal(true)

delete_if_exists(lib_path)
_ = shell("rmdir '{lib_dir}' 2>/dev/null || true")
```

</details>

#### writes binary data and supports empty payloads

- writes binary data and supports empty payloads
   - Expected: write_bytes_to_file(bytes_path, [72, 101, 108, 108, 111]) is true
   - Expected: write_bytes_to_file(empty_path, []) is true
   - Expected: rt_file_exists(bytes_path) is true
   - Expected: rt_file_exists(empty_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes binary data and supports empty payloads")
val bytes_path = "/tmp/unit_link_with_libraries_bytes.bin"
val empty_path = "/tmp/unit_link_with_libraries_empty.bin"
delete_if_exists(bytes_path)
delete_if_exists(empty_path)

expect(write_bytes_to_file(bytes_path, [72, 101, 108, 108, 111])).to_equal(true)
expect(write_bytes_to_file(empty_path, [])).to_equal(true)
expect(rt_file_exists(bytes_path)).to_equal(true)
expect(rt_file_exists(empty_path)).to_equal(true)

delete_if_exists(bytes_path)
delete_if_exists(empty_path)
```

</details>

#### extracts resolved object payloads to temporary files

- extracts resolved object payloads to temporary files
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().len() equals `1`
   - Expected: result.unwrap()[0] equals `obj_path`
   - Expected: rt_file_exists(obj_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts resolved object payloads to temporary files")
val temp_dir = "/tmp/unit_link_with_libraries_extract"
val obj_path = "{temp_dir}/simple_lib_pkg_core.o"
delete_if_exists(obj_path)
_ = shell("mkdir -p '{temp_dir}'")

val resolved = [
    ResolvedModule(
        module_name: "pkg/core",
        library_path: "/tmp/sample.lsm",
        smf_data: [10, 11, 12],
        has_object: true,
        obj_data: [127, 69, 76, 70, 1, 2, 3],
        has_code_units: false,
        code_units: []
    )
]

val result = extract_objects_from_resolved(resolved, temp_dir, false)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(1)
expect(result.unwrap()[0]).to_equal(obj_path)
expect(rt_file_exists(obj_path)).to_equal(true)

delete_if_exists(obj_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

#### rejects resolved modules that have no object payload

- rejects resolved modules that have no object payload
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects resolved modules that have no object payload")
val resolved = [
    ResolvedModule(
        module_name: "pkg/missing",
        library_path: "/tmp/sample.lsm",
        smf_data: [1],
        has_object: false,
        obj_data: [],
        has_code_units: false,
        code_units: []
    )
]

val result = extract_objects_from_resolved(resolved, "/tmp/unit_link_with_libraries_missing", false)
expect(result.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `750f773f104d501d4ee813b237f9c3e044f99459799f7871834bbb6f0f39615e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `750f773f104d501d4ee813b237f9c3e044f99459799f7871834bbb6f0f39615e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `750f773f104d501d4ee813b237f9c3e044f99459799f7871834bbb6f0f39615e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/link_with_libraries_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/link_with_libraries_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/link_with_libraries_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers libraries created on disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes binary data and supports empty payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts resolved object payloads to temporary files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
