# Content Authority Specification

> Reader clearance vs content authority level, plus revoked-trust deny.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Content Authority Specification

Reader clearance vs content authority level, plus revoked-trust deny.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/unit/lib/common/llm/content_authority_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reader clearance vs content authority level, plus revoked-trust deny.

## Scenarios

### Content Authority

### release_gate

#### AC-6: reader clearance >= content level → Release

- AC-6: reader clearance >= content level → Release


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: reader clearance >= content level → Release")
val content = ContentAuthority(level: AuthorityLevel.Internal, source_trust: TrustSource.RegistryTrusted)
val decision = release_gate(content, AuthorityLevel.Sensitive)
expect decision.kind to_equal "Release"
```

</details>

#### AC-6: equal clearance → Release

- AC-6: equal clearance → Release


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: equal clearance → Release")
val content = ContentAuthority(level: AuthorityLevel.Sensitive, source_trust: TrustSource.RegistryTrusted)
val decision = release_gate(content, AuthorityLevel.Sensitive)
expect decision.kind to_equal "Release"
```

</details>

#### AC-6: reader clearance < content level → Scrub or Block

- AC-6: reader clearance < content level → Scrub or Block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: reader clearance < content level → Scrub or Block")
val content = ContentAuthority(level: AuthorityLevel.Secret, source_trust: TrustSource.RegistryTrusted)
val decision = release_gate(content, AuthorityLevel.Public)
val held = (decision.kind == "Scrub") or (decision.kind == "Block")
expect held to_equal true
```

</details>

#### AC-6: revoked trust_source → Block

- AC-6: revoked trust_source → Block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: revoked trust_source → Block")
val content = ContentAuthority(level: AuthorityLevel.Public, source_trust: TrustSource.Revoked)
val decision = release_gate(content, AuthorityLevel.Secret)
expect decision.kind to_equal "Block"
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

- Canonical SPipe generation for source `fa53be4ab992ffbd5fd84f184448bfef5c3e41d2d7711225505669824af1a669`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa53be4ab992ffbd5fd84f184448bfef5c3e41d2d7711225505669824af1a669`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa53be4ab992ffbd5fd84f184448bfef5c3e41d2d7711225505669824af1a669`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/llm/content_authority_spec.spl
mirror: doc/06_spec/unit/lib/common/llm/content_authority_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/llm/content_authority_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/llm/content_authority_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/llm/content_authority_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: reader clearance >= content level → Release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/llm/content_authority_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: equal clearance → Release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/llm/content_authority_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: reader clearance < content level → Scrub or Block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
