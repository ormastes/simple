# native_cross_module_class_field_layout_regression_spec

> Native cross-module class field-layout regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_cross_module_class_field_layout_regression_spec

Native cross-module class field-layout regression.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native cross-module class field-layout regression.

## Scenarios

### native cross-module class field layout

#### writes the provider and entry modules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes the provider and entry modules
   - Expected: dir_create_all(BUILD_DIR) is true
   - Expected: file_write(PROVIDER_PATH, provider_source()) is true
   - Expected: file_write(ENTRY_PATH, entry_source()) is true
   - Expected: remove_file_if_exists(BINARY_PATH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes the provider and entry modules")
expect(dir_create_all(BUILD_DIR)).to_equal(true)
expect(file_write(PROVIDER_PATH, provider_source())).to_equal(true)
expect(file_write(ENTRY_PATH, entry_source())).to_equal(true)
expect(remove_file_if_exists(BINARY_PATH)).to_equal(true)
```

</details>

#### matches the interpreter oracle

- matches the interpreter oracle
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout equals `84`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches the interpreter oracle")
val result = shell("env -u SIMPLE_BOOTSTRAP bin/simple run " + ENTRY_PATH)
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_equal("84")
```

</details>

#### reads the provider field through the incremental native closure

- reads the provider field through the incremental native closure
   - Expected: compiled.exit_code equals `0`
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout equals `84`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads the provider field through the incremental native closure")
val compiled = shell(
    "env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 " +
    "bin/simple native-build --entry " + ENTRY_PATH +
    " --entry-closure --cache-dir " + CACHE_DIR + " -o " + BINARY_PATH
)
expect(compiled.exit_code).to_equal(0)

val result = shell(BINARY_PATH)
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_equal("84")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `07bdfac7727fc2b87267d73bf3d188d6c301275fcf0cc0b8751a534fb3f27b0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07bdfac7727fc2b87267d73bf3d188d6c301275fcf0cc0b8751a534fb3f27b0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07bdfac7727fc2b87267d73bf3d188d6c301275fcf0cc0b8751a534fb3f27b0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl
mirror: doc/06_spec/03_system/compiler/native_cross_module_class_field_layout_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_cross_module_class_field_layout_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_cross_module_class_field_layout_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes the provider and entry modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the interpreter oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the provider field through the incremental native closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
