# version_manifest_spec

> Canonical product versions remain one checked manifest with declared projections.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# version_manifest_spec

Canonical product versions remain one checked manifest with declared projections.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/version_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Canonical product versions remain one checked manifest with declared projections.

## Scenarios

### Canonical release version manifest

#### accepts matching release line and detects projection drift

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts matching release line and detects projection drift
- Validate the canonical version and line
- Check every declared projection
   - Expected: version_projection_drift(manifest, ["1.4.2", "1.4.1"]) equals `["src/app/simple.sdn"]`
   - Expected: version_undeclared_consumers(manifest, ["VERSION", "src/runtime/version.h"]) equals `["src/runtime/version.h"]`
   - Expected: version_render_plan(manifest) equals `["VERSION=1.4.2", "src/app/simple.sdn=1.4.2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts matching release line and detects projection drift")
step("Validate the canonical version and line")
val manifest = parse_version_manifest(version_fixture("1.4"))
expect(manifest.valid).to_be(true)
step("Check every declared projection")
expect(version_projection_drift(manifest, ["1.4.2", "1.4.1"])).to_equal(["src/app/simple.sdn"])
expect(version_undeclared_consumers(manifest, ["VERSION", "src/runtime/version.h"])).to_equal(["src/runtime/version.h"])
expect(version_render_plan(manifest)).to_equal(["VERSION=1.4.2", "src/app/simple.sdn=1.4.2"])
expect(version_explain(manifest)).to_contain("release/1.4")
```

</details>

#### rejects a release line that disagrees with semantic version

- rejects a release line that disagrees with semantic version
   - Expected: parse_version_manifest(version_fixture("1.5")).error equals `release line does not match semantic version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a release line that disagrees with semantic version")
expect(parse_version_manifest(version_fixture("1.5")).error).to_equal("release line does not match semantic version")
```

</details>

#### rejects malformed prerelease identifiers

- rejects malformed prerelease identifiers
   - Expected: parse_version_manifest(malformed).error equals `product, semver, line, or channel is invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects malformed prerelease identifiers")
val malformed = version_fixture("1.4").replace("1.4.2", "1.4.2-rc..1")
expect(parse_version_manifest(malformed).error).to_equal("product, semver, line, or channel is invalid")
expect(parse_version_manifest(version_fixture("1.4").replace("1.4.2", "01.4.2")).valid).to_be(false)
expect(parse_version_manifest(version_fixture("1.4").replace("1.4.2", "1.4.2-rc.01")).valid).to_be(false)
```

</details>

#### accepts the repository legacy RC spelling during migration

- accepts the repository legacy RC spelling during migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts the repository legacy RC spelling during migration")
val legacy = version_fixture("1.4").replace("1.4.2", "1.4.2-RC")
expect(parse_version_manifest(legacy).valid).to_be(true)
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

- `REQ-SSPEC-UNIT`
- `REQ-008`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42c9e50d4a6381c935aacf33c8eff99d2f8536266c57f0c3c3a26c3575cf0fad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42c9e50d4a6381c935aacf33c8eff99d2f8536266c57f0c3c3a26c3575cf0fad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42c9e50d4a6381c935aacf33c8eff99d2f8536266c57f0c3c3a26c3575cf0fad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/devhub/version_manifest_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/version_manifest_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/devhub/version_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/version_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/version_manifest_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/devhub/version_manifest_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts matching release line and detects projection drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/version_manifest_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a release line that disagrees with semantic version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/version_manifest_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed prerelease identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
