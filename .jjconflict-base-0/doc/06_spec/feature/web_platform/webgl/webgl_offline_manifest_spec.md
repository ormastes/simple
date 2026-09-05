# Webgl Offline Manifest Specification

> Tests covering WebGL offline conformance manifest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgl Offline Manifest Specification

## Scenarios

### WebGL offline conformance manifest

#### fixture exists and declares a non-empty offline slice

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fixture exists and declares a non-empty offline slice
   - Expected: rt_file_exists(MANIFEST_PATH) is true
   - Expected: manifest contains `(webgl_offline_conformance_manifest`
   - Expected: _entry_count(manifest) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fixture exists and declares a non-empty offline slice")
val manifest = _read(MANIFEST_PATH)
expect(rt_file_exists(MANIFEST_PATH)).to_equal(true)
expect(manifest.contains("(webgl_offline_conformance_manifest")).to_equal(true)
expect(_entry_count(manifest)).to_equal(5)
```

</details>

#### keeps every manifest entry offline deterministic and inline

- keeps every manifest entry offline deterministic and inline
   - Expected: _all_entries_have_offline_contract(manifest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps every manifest entry offline deterministic and inline")
val manifest = _read(MANIFEST_PATH)
expect(_all_entries_have_offline_contract(manifest)).to_equal(true)
```

</details>

#### contains no external URL references anywhere in the fixture

- contains no external URL references anywhere in the fixture
   - Expected: _has_external_url(manifest) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("contains no external URL references anywhere in the fixture")
val manifest = _read(MANIFEST_PATH)
expect(_has_external_url(manifest)).to_equal(false)
```

</details>

#### uses unique deterministic ids for each entry

- uses unique deterministic ids for each entry
   - Expected: _all_entry_ids_are_unique(manifest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses unique deterministic ids for each entry")
val manifest = _read(MANIFEST_PATH)
expect(_all_entry_ids_are_unique(manifest)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/webgl/webgl_offline_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WebGL offline conformance manifest.
- WebGL offline conformance manifest

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `584768b2eaf500dc1392452c363592d21fa06b4768efb851809eb3de4b1ae6db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `584768b2eaf500dc1392452c363592d21fa06b4768efb851809eb3de4b1ae6db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `584768b2eaf500dc1392452c363592d21fa06b4768efb851809eb3de4b1ae6db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/web_platform/webgl/webgl_offline_manifest_spec.spl
mirror: doc/06_spec/feature/web_platform/webgl/webgl_offline_manifest_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/webgl/webgl_offline_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/webgl/webgl_offline_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/webgl/webgl_offline_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/webgl/webgl_offline_manifest_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture exists and declares a non-empty offline slice' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgl/webgl_offline_manifest_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every manifest entry offline deterministic and inline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgl/webgl_offline_manifest_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains no external URL references anywhere in the fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
