# Claude Full tagged ID

> Pure Simple coverage for API-compatible tagged UUID IDs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full tagged ID

Pure Simple coverage for API-compatible tagged UUID IDs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/tagged_id_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for API-compatible tagged UUID IDs.

## Scenarios

### Claude full tagged ID

#### encodes UUIDs with tag, version, and fixed base58 body

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes UUIDs with tag, version, and fixed base58 body
- Encode normal UUID
   - Expected: toTaggedId("user", "550e8400-e29b-41d4-a716-446655440000") equals `user_01BWBeN28Vb7cMEx7Ym8AUzs`
- Encode zero and max UUIDs
   - Expected: toTaggedId("org", "00000000-0000-0000-0000-000000000000") equals `org_011111111111111111111111`
   - Expected: toTaggedId("user", "00000000-0000-0000-0000-000000000001") equals `user_011111111111111111111112`
   - Expected: toTaggedId("acc", "ffffffff-ffff-ffff-ffff-ffffffffffff") equals `acc_01YcVfxkQb6JRzqk5kF2tNLv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes UUIDs with tag, version, and fixed base58 body")
step("Encode normal UUID")
expect(toTaggedId("user", "550e8400-e29b-41d4-a716-446655440000")).to_equal("user_01BWBeN28Vb7cMEx7Ym8AUzs")

step("Encode zero and max UUIDs")
expect(toTaggedId("org", "00000000-0000-0000-0000-000000000000")).to_equal("org_011111111111111111111111")
expect(toTaggedId("user", "00000000-0000-0000-0000-000000000001")).to_equal("user_011111111111111111111112")
expect(toTaggedId("acc", "ffffffff-ffff-ffff-ffff-ffffffffffff")).to_equal("acc_01YcVfxkQb6JRzqk5kF2tNLv")
```

</details>

#### accepts UUIDs without hyphens and rejects invalid UUID hex

- accepts UUIDs without hyphens and rejects invalid UUID hex
- Encode compact UUID
   - Expected: toTaggedId("user", "550e8400e29b41d4a716446655440000") equals `user_01BWBeN28Vb7cMEx7Ym8AUzs`
- Reject invalid shape
   - Expected: toTaggedId("user", "550e8400-e29b-41d4-a716-44665544000g") equals ``
   - Expected: toTaggedId("user", "short") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts UUIDs without hyphens and rejects invalid UUID hex")
step("Encode compact UUID")
expect(toTaggedId("user", "550e8400e29b41d4a716446655440000")).to_equal("user_01BWBeN28Vb7cMEx7Ym8AUzs")

step("Reject invalid shape")
expect(toTaggedId("user", "550e8400-e29b-41d4-a716-44665544000g")).to_equal("")
expect(toTaggedId("user", "short")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `eafbbb2d33891cf2e6a4d9c3b375ea38759be5b82a19b237443e6652d879a940`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eafbbb2d33891cf2e6a4d9c3b375ea38759be5b82a19b237443e6652d879a940`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eafbbb2d33891cf2e6a4d9c3b375ea38759be5b82a19b237443e6652d879a940`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/app/llm_caret/tagged_id_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/tagged_id_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/tagged_id_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/tagged_id_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/tagged_id_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes UUIDs with tag, version, and fixed base58 body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/tagged_id_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts UUIDs without hyphens and rejects invalid UUID hex' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
