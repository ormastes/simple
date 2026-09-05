# Claude Full generated files

> Pure Simple coverage for generated-file attribution exclusion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full generated files

Pure Simple coverage for generated-file attribution exclusion.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/generated_files_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for generated-file attribution exclusion.

## Scenarios

### Claude full generated files

#### excludes lockfiles by case-insensitive basename

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- excludes lockfiles by case-insensitive basename
- Check exact filename exclusions
   - Expected: isGeneratedFile("package-lock.json") is true
   - Expected: isGeneratedFile("src/Cargo.lock") is true
   - Expected: isGeneratedFile("src/main.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes lockfiles by case-insensitive basename")
step("Check exact filename exclusions")
expect(isGeneratedFile("package-lock.json")).to_equal(true)
expect(isGeneratedFile("src/Cargo.lock")).to_equal(true)
expect(isGeneratedFile("src/main.spl")).to_equal(false)
```

</details>

#### excludes compound generated extensions

- excludes compound generated extensions
- Check compound extensions
   - Expected: isGeneratedFile("web/app.min.js") is true
   - Expected: isGeneratedFile("web/app.bundle.css") is true
   - Expected: isGeneratedFile("types/index.d.ts") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes compound generated extensions")
step("Check compound extensions")
expect(isGeneratedFile("web/app.min.js")).to_equal(true)
expect(isGeneratedFile("web/app.bundle.css")).to_equal(true)
expect(isGeneratedFile("types/index.d.ts")).to_equal(true)
```

</details>

#### excludes generated and vendor directories

- excludes generated and vendor directories
- Check path directory markers
   - Expected: isGeneratedFile("src/vendor/sqlite.c") is true
   - Expected: isGeneratedFile("pkg\\node_modules\\leftpad\\index.js") is true
   - Expected: isGeneratedFile("target/debug/app.o") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes generated and vendor directories")
step("Check path directory markers")
expect(isGeneratedFile("src/vendor/sqlite.c")).to_equal(true)
expect(isGeneratedFile("pkg\\node_modules\\leftpad\\index.js")).to_equal(true)
expect(isGeneratedFile("target/debug/app.o")).to_equal(true)
```

</details>

#### excludes generated filename patterns

- excludes generated filename patterns
- Check suffix and infix markers
   - Expected: isGeneratedFile("api/user.generated.ts") is true
   - Expected: isGeneratedFile("proto/service.pb.go") is true
   - Expected: isGeneratedFile("proto/service_pb2.py") is true
   - Expected: isGeneratedFile("api/client.openapi.ts") is true
   - Expected: isGeneratedFile("api/service.grpc.go") is true
   - Expected: isGeneratedFile("api/client.swagger.ts") is true
   - Expected: isGeneratedFile("api/schema.openapi.json") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes generated filename patterns")
step("Check suffix and infix markers")
expect(isGeneratedFile("api/user.generated.ts")).to_equal(true)
expect(isGeneratedFile("proto/service.pb.go")).to_equal(true)
expect(isGeneratedFile("proto/service_pb2.py")).to_equal(true)
expect(isGeneratedFile("api/client.openapi.ts")).to_equal(true)
expect(isGeneratedFile("api/service.grpc.go")).to_equal(true)
expect(isGeneratedFile("api/client.swagger.ts")).to_equal(true)
expect(isGeneratedFile("api/schema.openapi.json")).to_equal(true)
```

</details>

#### filters generated files from a list

- filters generated files from a list
- Check list filter
   - Expected: filtered.len() equals `2`
   - Expected: filtered[0] equals `src/main.spl`
   - Expected: filtered[1] equals `src/lib.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters generated files from a list")
step("Check list filter")
val files = ["src/main.spl", "dist/app.js", "README.generated.md", "src/lib.spl"]
val filtered = filterGeneratedFiles(files)
expect(filtered.len()).to_equal(2)
expect(filtered[0]).to_equal("src/main.spl")
expect(filtered[1]).to_equal("src/lib.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9368fb649cfae4d3324d2e81c24b5e685e49995f211b8e7d905d6c222695c95d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9368fb649cfae4d3324d2e81c24b5e685e49995f211b8e7d905d6c222695c95d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9368fb649cfae4d3324d2e81c24b5e685e49995f211b8e7d905d6c222695c95d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/utils/generated_files_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/generated_files_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/generated_files_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/generated_files_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/generated_files_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/generated_files_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes lockfiles by case-insensitive basename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/generated_files_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes compound generated extensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/generated_files_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes generated and vendor directories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
