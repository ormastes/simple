# native_struct_field_access_regression_spec

> Native struct-field access regression for the self-hosted AOT path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_struct_field_access_regression_spec

Native struct-field access regression for the self-hosted AOT path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_struct_field_access_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native struct-field access regression for the self-hosted AOT path.

## Scenarios

### self-hosted native struct field access

#### compiles and reads a text field from a local struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles and reads a text field from a local struct
- Write the minimal struct-field AOT repro
   - Expected: dir_create_all(BUILD_DIR) is true
   - Expected: remove_file_if_exists(BINARY_PATH) is true
- Compile through the deployed self-hosted native-build path
   - Expected: compiled.exit_code equals `0`
- Run the native artifact and observe the exact field value
   - Expected: ran.exit_code equals `0`
   - Expected: ran.stdout equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles and reads a text field from a local struct")
step("Write the minimal struct-field AOT repro")
expect(dir_create_all(BUILD_DIR)).to_equal(true)
expect(remove_file_if_exists(BINARY_PATH)).to_equal(true)
expect(file_write(
    SOURCE_PATH,
    "struct S:\n" +
    "    name: text\n" +
    "fn main():\n" +
    "    val v = S(name: \"A\")\n" +
    "    print(v.name)\n"
)).to_equal(true)

step("Compile through the deployed self-hosted native-build path")
val compiled = shell(
    "env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 " +
    "bin/simple native-build --entry " + SOURCE_PATH + " -o " + BINARY_PATH + " --clean"
)
expect(compiled.exit_code).to_equal(0)

step("Run the native artifact and observe the exact field value")
val ran = shell(BINARY_PATH)
expect(ran.exit_code).to_equal(0)
expect(ran.stdout).to_equal("A")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `4349563b81d8ea122e2368a6bcfff38ae62d9cd42e52c1e03c7f6c5ea53d6324`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4349563b81d8ea122e2368a6bcfff38ae62d9cd42e52c1e03c7f6c5ea53d6324`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4349563b81d8ea122e2368a6bcfff38ae62d9cd42e52c1e03c7f6c5ea53d6324`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/compiler/native_struct_field_access_regression_spec.spl
mirror: doc/06_spec/03_system/compiler/native_struct_field_access_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_struct_field_access_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_struct_field_access_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_struct_field_access_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/native_struct_field_access_regression_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles and reads a text field from a local struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
