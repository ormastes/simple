# sbom_cli_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sbom_cli_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sbom_cli_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/app/sbom_cli_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### sbom CLI handler — generates SBOM JSON

#### produces an output file containing the discovered file entries

- Verify: produces an output file containing the discovered file entries
   - Expected: code equals `0`
   - Expected: file_exists(out_path) is true
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: produces an output file containing the discovered file entries")
setup_fixture()
val out_path = "{TMP_OUT_DIR}/sbom_entries.spdx.json"
val code = run_sbom([TMP_ROOT, "--out={out_path}"])
expect(code).to_equal(0)
expect(file_exists(out_path)).to_equal(true)
val json = read_file(out_path)
expect(json).to_contain("\"spdxVersion\": \"SPDX-2.3\"")
expect(json).to_contain("a.spl")
expect(json).to_contain("b.spl")
expect(json).to_contain("c.spl")
expect(json).to_contain("\"checksumValue\"")
expect(json).to_contain("\"algorithm\": \"SHA256\"")

val capture = UntypedCapture(label: "sbom-entries-json", raw_value: json, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "sbom_cli_spec/sbom-entries-json")
val comparison = compare_evidence(evidence, oracle_spec("sbom_cli_spec/sbom-entries-json", [
    check_exact("value", "{\"spdxVersion\": \"SPDX-2.3\",\"dataLicense\": \"CC0-1.0\",\"SPDXID\": \"SPDXRef-DOCUMENT\",\"name\": \"ormastes.simple\",\"documentNamespace\": \"https://spdx.org/spdxdocs/ormastes.simple-0.1.0\",\"creationInfo\": {\"creators\": [\"Tool: simple-sbom-0.1\"],\"created\": \"\"},\"packages\": [{\"SPDXID\": \"SPDXRef-Package-Root\",\"name\": \"ormastes.simple\",\"versionInfo\": \"0.1.0\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": []},{\"SPDXID\": \"SPDXRef-Package-File-0\",\"name\": \"{TMP_ROOT}/a.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"f7f9a94208f8cef9ff2f49d03db6d1e5d0fd32492bc45aa2792a2a813759114b\"}]},{\"SPDXID\": \"SPDXRef-Package-File-1\",\"name\": \"{TMP_ROOT}/b.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"e9d4ef20cf5564fd8317a400d2bb857b22bf05358cfb7ff1657639979cb6612b\"}]},{\"SPDXID\": \"SPDXRef-Package-File-2\",\"name\": \"{TMP_ROOT}/c.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"cd9364e9502a349881609221d26e6c2b3ff2cec3d51e99eabeac516bf0616bf6\"}]}],\"relationships\": [{\"spdxElementId\": \"SPDXRef-DOCUMENT\",\"relationshipType\": \"DESCRIBES\",\"relatedSpdxElement\": \"SPDXRef-Package-Root\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-0\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-1\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-2\"}]}")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

#### honors --name= and --version= overrides

- Verify: honors --name= and --version= overrides
   - Expected: code equals `0`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: honors --name= and --version= overrides")
setup_fixture()
val out_path = "{TMP_OUT_DIR}/sbom_name.spdx.json"
val code = run_sbom([TMP_ROOT, "--out={out_path}", "--name=my.pkg", "--version=9.9.9"])
expect(code).to_equal(0)
val json = read_file(out_path)
expect(json).to_contain("\"name\": \"my.pkg\"")
expect(json).to_contain("my.pkg-9.9.9")

val capture = UntypedCapture(label: "sbom-name-version-json", raw_value: json, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "sbom_cli_spec/sbom-name-version-json")
val comparison = compare_evidence(evidence, oracle_spec("sbom_cli_spec/sbom-name-version-json", [
    check_exact("value", "{\"spdxVersion\": \"SPDX-2.3\",\"dataLicense\": \"CC0-1.0\",\"SPDXID\": \"SPDXRef-DOCUMENT\",\"name\": \"my.pkg\",\"documentNamespace\": \"https://spdx.org/spdxdocs/my.pkg-9.9.9\",\"creationInfo\": {\"creators\": [\"Tool: simple-sbom-0.1\"],\"created\": \"\"},\"packages\": [{\"SPDXID\": \"SPDXRef-Package-Root\",\"name\": \"my.pkg\",\"versionInfo\": \"9.9.9\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": []},{\"SPDXID\": \"SPDXRef-Package-File-0\",\"name\": \"{TMP_ROOT}/a.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"f7f9a94208f8cef9ff2f49d03db6d1e5d0fd32492bc45aa2792a2a813759114b\"}]},{\"SPDXID\": \"SPDXRef-Package-File-1\",\"name\": \"{TMP_ROOT}/b.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"e9d4ef20cf5564fd8317a400d2bb857b22bf05358cfb7ff1657639979cb6612b\"}]},{\"SPDXID\": \"SPDXRef-Package-File-2\",\"name\": \"{TMP_ROOT}/c.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"cd9364e9502a349881609221d26e6c2b3ff2cec3d51e99eabeac516bf0616bf6\"}]}],\"relationships\": [{\"spdxElementId\": \"SPDXRef-DOCUMENT\",\"relationshipType\": \"DESCRIBES\",\"relatedSpdxElement\": \"SPDXRef-Package-Root\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-0\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-1\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-2\"}]}")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

### sbom CLI handler — determinism (certification requirement)

#### generating twice from identical inputs is byte-for-byte identical

- Verify: generating twice from identical inputs is byte-for-byte identical
   - Expected: code_1 equals `0`
   - Expected: code_2 equals `0`
   - Expected: json_1 equals `json_2`
   - Expected: json_1.len() > 0 is true
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: generating twice from identical inputs is byte-for-byte identical")
# @req: REQ-SSPEC-LOCAL-001
setup_fixture()
val out_path_1 = "{TMP_OUT_DIR}/sbom_run1.spdx.json"
val out_path_2 = "{TMP_OUT_DIR}/sbom_run2.spdx.json"
val code_1 = run_sbom([TMP_ROOT, "--out={out_path_1}"])
val code_2 = run_sbom([TMP_ROOT, "--out={out_path_2}"])
expect(code_1).to_equal(0)
expect(code_2).to_equal(0)
val json_1 = read_file(out_path_1)
val json_2 = read_file(out_path_2)
expect(json_1).to_equal(json_2)
expect(json_1.len() > 0).to_equal(true)

val capture = UntypedCapture(label: "sbom-determinism-run1-json", raw_value: json_1, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "sbom_cli_spec/sbom-determinism-run1-json")
val comparison = compare_evidence(evidence, oracle_spec("sbom_cli_spec/sbom-determinism-run1-json", [
    check_exact("value", "{\"spdxVersion\": \"SPDX-2.3\",\"dataLicense\": \"CC0-1.0\",\"SPDXID\": \"SPDXRef-DOCUMENT\",\"name\": \"ormastes.simple\",\"documentNamespace\": \"https://spdx.org/spdxdocs/ormastes.simple-0.1.0\",\"creationInfo\": {\"creators\": [\"Tool: simple-sbom-0.1\"],\"created\": \"\"},\"packages\": [{\"SPDXID\": \"SPDXRef-Package-Root\",\"name\": \"ormastes.simple\",\"versionInfo\": \"0.1.0\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": []},{\"SPDXID\": \"SPDXRef-Package-File-0\",\"name\": \"{TMP_ROOT}/a.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"f7f9a94208f8cef9ff2f49d03db6d1e5d0fd32492bc45aa2792a2a813759114b\"}]},{\"SPDXID\": \"SPDXRef-Package-File-1\",\"name\": \"{TMP_ROOT}/b.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"e9d4ef20cf5564fd8317a400d2bb857b22bf05358cfb7ff1657639979cb6612b\"}]},{\"SPDXID\": \"SPDXRef-Package-File-2\",\"name\": \"{TMP_ROOT}/c.spl\",\"versionInfo\": \"NOASSERTION\",\"downloadLocation\": \"NOASSERTION\",\"filesAnalyzed\": true,\"checksums\": [{\"algorithm\": \"SHA256\",\"checksumValue\": \"cd9364e9502a349881609221d26e6c2b3ff2cec3d51e99eabeac516bf0616bf6\"}]}],\"relationships\": [{\"spdxElementId\": \"SPDXRef-DOCUMENT\",\"relationshipType\": \"DESCRIBES\",\"relatedSpdxElement\": \"SPDXRef-Package-Root\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-0\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-1\"},{\"spdxElementId\": \"SPDXRef-Package-Root\",\"relationshipType\": \"CONTAINS\",\"relatedSpdxElement\": \"SPDXRef-Package-File-2\"}]}")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26864723385499e24be99546f39aef7a206af90af13494b4885c5fa81465311d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26864723385499e24be99546f39aef7a206af90af13494b4885c5fa81465311d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26864723385499e24be99546f39aef7a206af90af13494b4885c5fa81465311d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/app/sbom_cli_spec.spl
mirror: doc/06_spec/01_unit/app/sbom_cli_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/sbom_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sbom_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/sbom_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/app/sbom_cli_spec.spl. -->
