# native_platform_path_owner_regression_spec

> Native platform path-owner regression for strict self-hosted AOT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_platform_path_owner_regression_spec

Native platform path-owner regression for strict self-hosted AOT.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_platform_path_owner_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native platform path-owner regression for strict self-hosted AOT.

## Scenarios

### self-hosted native platform path ownership

#### links real named path owners without a module global or fallback stub

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- links real named path owners without a module global or fallback stub
- Write the real platform-facade path probe
   - Expected: dir_create_all(BUILD_DIR) is true
   - Expected: remove_file_if_exists(BINARY_PATH) is true
- Compile through strict self-hosted entry closure
   - Expected: compiled.exit_code equals `0`
   - Expected: compiled.stderr does not contain `undeclared symbol`
   - Expected: compiled.stderr does not contain `generated stub`
- Run the native artifact
   - Expected: ran.exit_code equals `0`
   - Expected: ran.stdout equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("links real named path owners without a module global or fallback stub")
step("Write the real platform-facade path probe")
expect(dir_create_all(BUILD_DIR)).to_equal(true)
expect(remove_file_if_exists(BINARY_PATH)).to_equal(true)
expect(file_write(
    SOURCE_PATH,
    "use nogc_sync_mut.platform.{normalize_path, is_absolute_path, join_path}\n" +
    "fn main():\n" +
    "    if normalize_path(\"alpha\\\\beta\") == \"alpha/beta\" and is_absolute_path(\"/tmp/simple\") and join_path(\"alpha\", \"beta\") == \"alpha/beta\":\n" +
    "        print 42\n" +
    "    else:\n" +
    "        print 1\n"
)).to_equal(true)

step("Compile through strict self-hosted entry closure")
val compiled = shell(
    "env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 " +
    "bin/simple native-build --entry " + SOURCE_PATH + " -o " + BINARY_PATH + " --clean"
)
expect(compiled.exit_code).to_equal(0)
expect(compiled.stderr.contains("undeclared symbol")).to_equal(false)
expect(compiled.stderr.contains("generated stub")).to_equal(false)

step("Run the native artifact")
val ran = shell(BINARY_PATH)
expect(ran.exit_code).to_equal(0)
expect(ran.stdout).to_equal("42")
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

- Canonical SPipe generation for source `df3a805b33734c07b339b6eb95f130cd3ad9808cc2523b810f19cb11fd4f80ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df3a805b33734c07b339b6eb95f130cd3ad9808cc2523b810f19cb11fd4f80ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df3a805b33734c07b339b6eb95f130cd3ad9808cc2523b810f19cb11fd4f80ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/compiler/native_platform_path_owner_regression_spec.spl
mirror: doc/06_spec/03_system/compiler/native_platform_path_owner_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_platform_path_owner_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_platform_path_owner_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_platform_path_owner_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/native_platform_path_owner_regression_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links real named path owners without a module global or fallback stub' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
