# Ide Plugin Manifest Harden Specification

> Tests covering plugin_manifest: validation catches empty name and duplicate entries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Plugin Manifest Harden Specification

## Scenarios

### plugin_manifest: validation catches empty name and duplicate entries

#### standard IDE plugin entries are all valid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- standard IDE plugin entries are all valid
   - Expected: ide_plugin_manifest_is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("standard IDE plugin entries are all valid")
expect(ide_plugin_manifest_is_valid()).to_equal(true)
```

</details>

#### manifest validate returns empty string for valid entries

- manifest validate returns empty string for valid entries
   - Expected: ide_plugin_manifest_validate(entries) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manifest validate returns empty string for valid entries")
val entries = ide_plugin_entries()
expect(ide_plugin_manifest_validate(entries)).to_equal("")
```

</details>

#### roundtrip count matches entry count

- roundtrip count matches entry count
   - Expected: probe.roundtrip_count equals `probe.entry_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrip count matches entry count")
val probe = ide_plugin_manifest_probe()
expect(probe.roundtrip_count).to_equal(probe.entry_count)
```

</details>

#### all manifest names are non-empty

- all manifest names are non-empty
   - Expected: all_nonempty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all manifest names are non-empty")
val probe = ide_plugin_manifest_probe()
var all_nonempty = true
for name in probe.names:
    if name == "":
        all_nonempty = false
expect(all_nonempty).to_equal(true)
```

</details>

#### entry count is positive

- entry count is positive
   - Expected: probe.entry_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entry count is positive")
val probe = ide_plugin_manifest_probe()
expect(probe.entry_count > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_plugin_manifest_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering plugin_manifest: validation catches empty name and duplicate entries.
- plugin_manifest: validation catches empty name and duplicate entries

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe1be8c4ccf0d9f571c0259ec9201b9829782edca25936696988c8feb610a2ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe1be8c4ccf0d9f571c0259ec9201b9829782edca25936696988c8feb610a2ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe1be8c4ccf0d9f571c0259ec9201b9829782edca25936696988c8feb610a2ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ide/ide_plugin_manifest_harden_spec.spl
mirror: doc/06_spec/01_unit/app/ide/ide_plugin_manifest_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ide/ide_plugin_manifest_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ide/ide_plugin_manifest_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ide/ide_plugin_manifest_harden_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'standard IDE plugin entries are all valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_plugin_manifest_harden_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'manifest validate returns empty string for valid entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_plugin_manifest_harden_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'roundtrip count matches entry count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
