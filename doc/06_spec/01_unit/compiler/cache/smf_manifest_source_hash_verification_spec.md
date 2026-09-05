# SMF Manifest Source-Hash Verification Specification

> `SmfManifestEntry` records `source_hash` at compile time, but until 2026-08-17 `try_load_smf_cached` parsed every recorded field and used only `smf_path` — the manifest row itself was never verified. `smf_manifest_entry_matches_source` is the fail-closed predicate that now gates the cache hit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Manifest Source-Hash Verification Specification

`SmfManifestEntry` records `source_hash` at compile time, but until 2026-08-17 `try_load_smf_cached` parsed every recorded field and used only `smf_path` — the manifest row itself was never verified. `smf_manifest_entry_matches_source` is the fail-closed predicate that now gates the cache hit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`SmfManifestEntry` records `source_hash` at compile time, but until 2026-08-17
`try_load_smf_cached` parsed every recorded field and used only `smf_path` —
the manifest row itself was never verified. `smf_manifest_entry_matches_source`
is the fail-closed predicate that now gates the cache hit.

Fail-closed contract:
  - `source_hash == 0` (the sentinel both writers record when the source could
    not be read at compile time) is NEVER trusted, even against empty source.
  - unreadable / empty live source is NEVER trusted.
  - any hash mismatch rejects.
  - only a non-zero recorded hash equal to the live hash accepts.

## Scenarios

### smf_manifest_entry_matches_source

#### rejects an entry whose recorded hash does not match the live source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an entry whose recorded hash does not match the live source
   - Expected: smf_manifest_entry_matches_source(e, src) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an entry whose recorded hash does not match the live source")
val src = "fn main(): print \"hi\"\n"
val e = entry_with_hash(1234567)
expect(smf_manifest_entry_matches_source(e, src)).to_equal(false)
```

</details>

#### rejects the zero source_hash sentinel against matching content

- rejects the zero source_hash sentinel against matching content
   - Expected: smf_manifest_entry_matches_source(e, "anything") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the zero source_hash sentinel against matching content")
# The writers record 0 when the source could not be read. A 0 must
# never authorise a cache hit, however the live source hashes.
val e = entry_with_hash(0)
expect(smf_manifest_entry_matches_source(e, "anything")).to_equal(false)
```

</details>

#### rejects the zero source_hash sentinel against empty content

- rejects the zero source_hash sentinel against empty content
   - Expected: smf_manifest_entry_matches_source(e, "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the zero source_hash sentinel against empty content")
val e = entry_with_hash(0)
expect(smf_manifest_entry_matches_source(e, "")).to_equal(false)
```

</details>

#### rejects when the live source is unreadable (empty text)

- rejects when the live source is unreadable (empty text)
   - Expected: smf_manifest_entry_matches_source(e, "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when the live source is unreadable (empty text)")
val e = entry_with_hash(1234567)
expect(smf_manifest_entry_matches_source(e, "")).to_equal(false)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4001296469bce770ba9f7dbbc992f9145d1e2d3b823134ff2df64426524e511e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4001296469bce770ba9f7dbbc992f9145d1e2d3b823134ff2df64426524e511e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4001296469bce770ba9f7dbbc992f9145d1e2d3b823134ff2df64426524e511e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an entry whose recorded hash does not match the live source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the zero source_hash sentinel against matching content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the zero source_hash sentinel against empty content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
