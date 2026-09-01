# lifecycle_codec_spec

> Lifecycle persistence envelopes round-trip exact fields and reject tampering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_codec_spec

Lifecycle persistence envelopes round-trip exact fields and reject tampering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/scv/lifecycle_codec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lifecycle persistence envelopes round-trip exact fields and reject tampering.

## Scenarios

### SCV lifecycle record codec

#### round-trips the complete canonical field vector

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips the complete canonical field vector
- Encode a provider-neutral lifecycle record
- Decode and retain every field
   - Expected: decoded.record.?.fields equals `["REV-1", "rev_head", "reviewer", "policy-digest", "evidence-digest", "approv... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips the complete canonical field vector")
step("Encode a provider-neutral lifecycle record")
val encoded = lifecycle_record_encode(lifecycle_record("approval", "APR-1", ["REV-1", "rev_head", "reviewer", "policy-digest", "evidence-digest", "approved"]))
expect(encoded).to_start_with("scv-lifecycle/1|approval|APR-1|")
step("Decode and retain every field")
val decoded = lifecycle_record_decode(encoded)
expect(decoded.ok).to_be(true)
expect(decoded.record != nil).to_be(true)
expect(decoded.record.?.fields).to_equal(["REV-1", "rev_head", "reviewer", "policy-digest", "evidence-digest", "approved"])
```

</details>

#### rejects a tampered digest

- rejects a tampered digest
   - Expected: lifecycle_record_decode(encoded + "tampered").error equals `lifecycle digest mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a tampered digest")
val encoded = lifecycle_record_encode(lifecycle_record("change", "CHG-1", ["title", "owner"]))
expect(lifecycle_record_decode(encoded + "tampered").error).to_equal("lifecycle digest mismatch")
```

</details>

#### rejects unsafe delimiter-bearing fields before persistence

- rejects unsafe delimiter-bearing fields before persistence
   - Expected: lifecycle_record_encode(lifecycle_record("task", "TASK-1", ["unsafe|field"])) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unsafe delimiter-bearing fields before persistence")
expect(lifecycle_record_encode(lifecycle_record("task", "TASK-1", ["unsafe|field"]))).to_equal("")
```

</details>

#### persists and reloads an exact lifecycle envelope

- persists and reloads an exact lifecycle envelope
- Write through the lifecycle store facade
- Read and verify the stored digest
   - Expected: decoded.record.?.digest equals `record.digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("persists and reloads an exact lifecycle envelope")
step("Write through the lifecycle store facade")
val record = lifecycle_record("change", "CHG-CODEC-1", ["title", "owner", "intent-digest"])
val root = "build/test-artifacts/scv-lifecycle-codec"
expect(lifecycle_store_path(root, record)).to_end_with("/.scv/lifecycle/change/CHG-CODEC-1.scvl")
expect(lifecycle_store_write(root, record)).to_be(true)
step("Read and verify the stored digest")
val decoded = lifecycle_store_read(root, "change", "CHG-CODEC-1")
expect(decoded.ok).to_be(true)
expect(decoded.record.?.digest).to_equal(record.digest)
```

</details>

#### distinguishes absent records from corrupt stored envelopes

- distinguishes absent records from corrupt stored envelopes
   - Expected: lifecycle_store_probe(root, "change", "CHG-MISSING").status equals `absent`
   - Expected: lifecycle_store_probe(root, "change", "CHG-CORRUPT").status equals `corrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes absent records from corrupt stored envelopes")
val root = "build/test-artifacts/scv-lifecycle-codec-probe"
val record = lifecycle_record("change", "CHG-CORRUPT", ["title", "owner", "intent"])
expect(lifecycle_store_probe(root, "change", "CHG-MISSING").status).to_equal("absent")
expect(lifecycle_store_write(root, record)).to_be(true)
expect(file_write(lifecycle_store_path(root, record), "corrupt")).to_be(true)
expect(lifecycle_store_probe(root, "change", "CHG-CORRUPT").status).to_equal("corrupt")
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

- `REQ-SSPEC-UNIT`
- `REQ-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `504eb15199f456e1adaf1eee87c6a069cd93167224a5ed9e496e69ffd88eeebb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `504eb15199f456e1adaf1eee87c6a069cd93167224a5ed9e496e69ffd88eeebb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `504eb15199f456e1adaf1eee87c6a069cd93167224a5ed9e496e69ffd88eeebb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/scv/lifecycle_codec_spec.spl
mirror: doc/06_spec/01_unit/lib/scv/lifecycle_codec_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/scv/lifecycle_codec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/scv/lifecycle_codec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/scv/lifecycle_codec_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/scv/lifecycle_codec_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips the complete canonical field vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_codec_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a tampered digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_codec_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsafe delimiter-bearing fields before persistence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
