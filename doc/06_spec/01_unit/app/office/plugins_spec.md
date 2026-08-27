# plugins_spec

> Office plugin registration spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# plugins_spec

Office plugin registration spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/plugins_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office plugin registration spec.

Verifies that Word, PPT (slides), and Excel (sheets) are registered as three
SEPARATE plugins layered on the shared markdown / CSS substrate, using the
project's existing plugin registry manifest format — the "word/ppt/excel as
separate plugins on the md module" slice of the LibreOffice suite.

The manifest is built, serialized, and parsed back, proving it round-trips
through the shared registry; all assertions are over plugin names / counts and
so run cleanly on the test runner.

## Scenarios

### office plugins: three separate plugins on the shared module

#### registers exactly three office plugins

- registers exactly three office plugins
   - Expected: office_plugin_names().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("registers exactly three office plugins")
expect(office_plugin_names().len()).to_equal(3)
```

</details>

#### names the word, ppt, and excel plugins

- names the word, ppt, and excel plugins


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("names the word, ppt, and excel plugins")
val names = office_plugin_names()
expect(names).to_contain("office-word")
expect(names).to_contain("office-ppt")
expect(names).to_contain("office-excel")
```

</details>

### office plugins: manifest round-trips and validates

#### round-trips through the registry manifest format

- round-trips through the registry manifest format
   - Expected: probe.plugin_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("round-trips through the registry manifest format")
# plugin_count is the number of entries parsed back out of the manifest;
# equalling the 3 input entries proves the manifest round-trips.
val probe = office_plugin_manifest_probe()
expect(probe.plugin_count).to_equal(3)
```

</details>

#### is a well-formed manifest (validation returns no error)

- is a well-formed manifest (validation returns no error)
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is a well-formed manifest (validation returns no error)")
val err = office_plugin_validate(office_plugin_entries())
expect(err).to_equal("")
```

</details>

#### the serialized manifest names each plugin

- the serialized manifest names each plugin


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the serialized manifest names each plugin")
val probe = office_plugin_manifest_probe()
val manifest = probe.manifest_text
expect(manifest).to_contain("office-word")
expect(manifest).to_contain("office-ppt")
expect(manifest).to_contain("office-excel")
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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e1df70f0be13c2025ce1e5b860fc83fb92e3d2cc67340a6b7cabeafde2839f84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1df70f0be13c2025ce1e5b860fc83fb92e3d2cc67340a6b7cabeafde2839f84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1df70f0be13c2025ce1e5b860fc83fb92e3d2cc67340a6b7cabeafde2839f84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/office/plugins_spec.spl
mirror: doc/06_spec/01_unit/app/office/plugins_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/plugins_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/plugins_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/plugins_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/plugins_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers exactly three office plugins' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/plugins_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the word, ppt, and excel plugins' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/plugins_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips through the registry manifest format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
