# Spipe Docgen Evidence Wiring Specification

> Tests covering spipe_docgen typed-evidence wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Docgen Evidence Wiring Specification

## Scenarios

### spipe_docgen typed-evidence wiring

#### produces byte-identical output when no evidence sidecar exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces byte-identical output when no evidence sidecar exists
   - Expected: before equals `after`
   - Expected: before does not contain `## Typed Evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces byte-identical output when no evidence sidecar exists")
val out_dir = "/tmp/spipe_docgen_evidence_wiring_test_no_sidecar"
dir_create(out_dir, true)
val spec_path = out_dir + "/no_sidecar_spec.spl"
val sidecar_path = spec_path + ".evidence.sdn"
if file_exists(sidecar_path):
    file_delete(sidecar_path)

val before = read_output(out_dir, spec_path)
val after = read_output(out_dir, spec_path)

expect(before).to_equal(after)
expect(before.contains("## Typed Evidence")).to_equal(false)
```

</details>

#### renders typed-evidence blocks when a sidecar is present

- renders typed-evidence blocks when a sidecar is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders typed-evidence blocks when a sidecar is present")
val out_dir = "/tmp/spipe_docgen_evidence_wiring_test_with_sidecar"
dir_create(out_dir, true)
val spec_path = out_dir + "/with_sidecar_spec.spl"
val sidecar_path = spec_path + ".evidence.sdn"

val sha = "abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234"[0:64]
val sidecar_content =
    "schema=simple.sspec.evidence.v1\n" +
    "evidence_id=demo-1\n" +
    "profile_id=demo\n" +
    "spec_path=" + spec_path + "\n" +
    "spec_sha256=" + sha + "\n" +
    "provider_id=demo-provider\n" +
    "provider_version=1.0.0\n" +
    "run_id=run-1\n" +
    "environment=ci\n" +
    "artifact_sha256=" + sha + "\n" +
    "status=passed\n" +
    "---\n" +
    "kind=paragraph\n" +
    "title=Observed Output\n" +
    "audience=qa\n" +
    "line=hello typed evidence world\n"
file_atomic_write(sidecar_path, sidecar_content)

val rendered = read_output(out_dir, spec_path)

expect(rendered).to_contain("## Typed Evidence")
expect(rendered).to_contain("### Observed Output")
expect(rendered).to_contain("hello typed evidence world")

file_delete(sidecar_path)
```

</details>

#### renders a real Markdown pipe table from emit_evidence's binary word rows

- renders a real Markdown pipe table from emit_evidence's binary word rows
   - Expected: rendered does not contain `\\|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders a real Markdown pipe table from emit_evidence's binary word rows")
val out_dir = "/tmp/spipe_docgen_evidence_wiring_test_emit_evidence"
dir_create(out_dir, true)
val spec_path = out_dir + "/emit_evidence_spec.spl"
val sidecar_path = spec_path + ".evidence.sdn"
if file_exists(sidecar_path):
    file_delete(sidecar_path)

val rows = stacked_manual_rows([0xCAFEBABE], "W", 0)
emit_evidence(spec_path, "Binary evidence", rows)

val rendered = read_output(out_dir, spec_path)

expect(rendered).to_contain("## Typed Evidence")
expect(rendered).to_contain("### Binary evidence")
expect(rendered).to_contain("| Word | Value (hex) | Binary |")
expect(rendered).to_contain("| --- | --- | --- |")
expect(rendered).to_contain("| W0 | 0xbe ba fe ca 00 00 00 00 |")
expect(rendered.contains("\\|")).to_equal(false)

file_delete(sidecar_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spipe_docgen typed-evidence wiring.
- spipe_docgen typed-evidence wiring

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dace24eae345960617e3e39320701e19b2c8820bce74c7ed4b30c7adcab20231`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dace24eae345960617e3e39320701e19b2c8820bce74c7ed4b30c7adcab20231`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dace24eae345960617e3e39320701e19b2c8820bce74c7ed4b30c7adcab20231`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl
mirror: doc/06_spec/02_integration/app/spipe_docgen_evidence_wiring_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/spipe_docgen_evidence_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/spipe_docgen_evidence_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
