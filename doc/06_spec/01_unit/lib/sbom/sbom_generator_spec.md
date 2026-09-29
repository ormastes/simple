# sbom_generator_spec

> SBOM (Software Bill of Materials) generator spec — SPDX-2.3-minimal.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sbom_generator_spec

SBOM (Software Bill of Materials) generator spec — SPDX-2.3-minimal.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/sbom/sbom_generator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SBOM (Software Bill of Materials) generator spec — SPDX-2.3-minimal.

Mission-critical robustness campaign, lane sbom-emission. Covers the
decision-free slice: document model + deterministic JSON generator +
sha256 checksums (reusing std.common.crypto.sha256, not reimplemented).

CLI wiring into `bin/simple build` is OUT OF SCOPE — see sbom_generator.spl
header comment for the follow-up note.

## Scenarios

### SBOM generator — document skeleton (SPDX-2.3-minimal)

#### produces the required top-level SPDX fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces the required top-level SPDX fields
   - Expected: doc.spdx_version equals `SPDX-2.3`
   - Expected: doc.data_license equals `CC0-1.0`
   - Expected: doc.spdx_id equals `SPDXRef-DOCUMENT`
   - Expected: doc.name equals `ormastes.simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the required top-level SPDX fields")
setup_fixture_files()
val doc = generate_sbom_document(
    TMP_ROOT, "ormastes.simple", "0.1.0",
    ["a.spl"], [], ["Tool: simple-sbom-0.1"], ""
)
expect(doc.spdx_version).to_equal("SPDX-2.3")
expect(doc.data_license).to_equal("CC0-1.0")
expect(doc.spdx_id).to_equal("SPDXRef-DOCUMENT")
expect(doc.name).to_equal("ormastes.simple")
expect(doc.document_namespace).to_contain("ormastes.simple-0.1.0")
```

</details>

#### serialized JSON carries spdxVersion, name, and creationInfo.created verbatim

- serialized JSON carries spdxVersion, name, and creationInfo.created verbatim


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serialized JSON carries spdxVersion, name, and creationInfo.created verbatim")
setup_fixture_files()
val json = generate_sbom_json(
    TMP_ROOT, "ormastes.simple", "0.1.0",
    ["a.spl"], [], ["Tool: simple-sbom-0.1"], "2026-07-29T00:00:00Z"
)
expect(json).to_contain("\"spdxVersion\": \"SPDX-2.3\"")
expect(json).to_contain("\"name\": \"ormastes.simple\"")
expect(json).to_contain("\"created\": \"2026-07-29T00:00:00Z\"")
```

</details>

### SBOM generator — determinism (certification requirement)

#### generating twice from identical inputs is byte-for-byte identical

- generating twice from identical inputs is byte-for-byte identical
   - Expected: json_1 equals `json_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("generating twice from identical inputs is byte-for-byte identical")
setup_fixture_files()
val json_1 = generate_sbom_json(
    TMP_ROOT, "ormastes.simple", "0.1.0",
    ["a.spl"], ["vendor_thing.h"], ["Tool: simple-sbom-0.1"], ""
)
val json_2 = generate_sbom_json(
    TMP_ROOT, "ormastes.simple", "0.1.0",
    ["a.spl"], ["vendor_thing.h"], ["Tool: simple-sbom-0.1"], ""
)
expect(json_1).to_equal(json_2)
```

</details>

### SBOM generator — package entry with checksum

#### a tracked file's package entry carries its real sha256 hex digest

- a tracked file's package entry carries its real sha256 hex digest
   - Expected: expected_digest.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a tracked file's package entry carries its real sha256 hex digest")
setup_fixture_files()
val expected_digest = sha256_hex_of_file(TMP_ROOT, "a.spl")
# Same digest std.common.crypto.sha256 would produce directly —
# this asserts the generator REUSES that hasher, not a reimplementation.
expect(expected_digest.len()).to_equal(64)
val json = generate_sbom_json(
    TMP_ROOT, "ormastes.simple", "0.1.0",
    ["a.spl"], [], [], ""
)
expect(json).to_contain("\"name\": \"a.spl\"")
expect(json).to_contain("\"checksumValue\": \"{expected_digest}\"")
expect(json).to_contain("\"algorithm\": \"SHA256\"")
expect(json).to_contain("\"filesAnalyzed\": true")
```

</details>

### SBOM generator — vendored third-party component

#### a vendored file gets its own package plus a DEPENDS_ON relationship from the root package

- a vendored file gets its own package plus a DEPENDS_ON relationship from the root package
   - Expected: doc.packages.len() equals `2)  # root + vendor`
   - Expected: doc.relationships.len() equals `2)  # DESCRIBES + DEPENDS_ON`
   - Expected: depends_on.relationship_type equals `DEPENDS_ON`
   - Expected: depends_on.spdx_element_id equals `SPDXRef-Package-Root`
   - Expected: depends_on.related_spdx_element_id equals `SPDXRef-Package-Vendor-0`
   - Expected: vendor_pkg.name equals `vendor_thing.h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a vendored file gets its own package plus a DEPENDS_ON relationship from the root package")
setup_fixture_files()
val doc = generate_sbom_document(
    TMP_ROOT, "ormastes.simple", "0.1.0",
    [], ["vendor_thing.h"], [], ""
)
expect(doc.packages.len()).to_equal(2)  # root + vendor
expect(doc.relationships.len()).to_equal(2)  # DESCRIBES + DEPENDS_ON
val depends_on = doc.relationships[1]
expect(depends_on.relationship_type).to_equal("DEPENDS_ON")
expect(depends_on.spdx_element_id).to_equal("SPDXRef-Package-Root")
expect(depends_on.related_spdx_element_id).to_equal("SPDXRef-Package-Vendor-0")
val vendor_pkg = doc.packages[1]
expect(vendor_pkg.name).to_equal("vendor_thing.h")
```

</details>

### SBOM generator — empty-input edge case

#### no files and no vendored components still yields a valid single-package document

- no files and no vendored components still yields a valid single-package document
   - Expected: doc.packages.len() equals `1)  # root package only`
   - Expected: doc.relationships.len() equals `1)  # DESCRIBES only`
   - Expected: doc.packages[0].spdx_id equals `SPDXRef-Package-Root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no files and no vendored components still yields a valid single-package document")
val doc = generate_sbom_document(
    TMP_ROOT, "ormastes.simple", "0.1.0", [], [], [], ""
)
expect(doc.packages.len()).to_equal(1)  # root package only
expect(doc.relationships.len()).to_equal(1)  # DESCRIBES only
expect(doc.packages[0].spdx_id).to_equal("SPDXRef-Package-Root")
expect(doc.packages[0].files_analyzed).to_be(false)
val json = serialize_sbom(doc)
expect(json).to_contain("\"packages\": [")
expect(json).to_contain("\"relationships\": [")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02d9a6862b21826ecac0dbf82974fd442a0e0d7ace54a8a9a7740bd5ec3662a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02d9a6862b21826ecac0dbf82974fd442a0e0d7ace54a8a9a7740bd5ec3662a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02d9a6862b21826ecac0dbf82974fd442a0e0d7ace54a8a9a7740bd5ec3662a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/sbom/sbom_generator_spec.spl
mirror: doc/06_spec/01_unit/lib/sbom/sbom_generator_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/sbom/sbom_generator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/sbom/sbom_generator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/sbom/sbom_generator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/sbom/sbom_generator_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the required top-level SPDX fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/sbom/sbom_generator_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serialized JSON carries spdxVersion, name, and creationInfo.created verbatim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/sbom/sbom_generator_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generating twice from identical inputs is byte-for-byte identical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
