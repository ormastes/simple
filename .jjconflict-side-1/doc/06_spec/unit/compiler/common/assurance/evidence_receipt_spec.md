# Evidence receipts

> `src/compiler/00.common/assurance/evidence_receipt.spl` is the frozen shape of a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Evidence receipts

`src/compiler/00.common/assurance/evidence_receipt.spl` is the frozen shape of a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md §Phase 9 |
| Research | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md §15, §19, §22, §23.9 |
| Source | `test/unit/compiler/common/assurance/evidence_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`src/compiler/00.common/assurance/evidence_receipt.spl` is the frozen shape of a
Phase 9 evidence receipt: a gate's verbatim verdict line bound to the sha256 of
the artifact it examined and the sha256 of the seal it was examined against,
with the time it was produced. §23.9 says a report is not evidence; this is what
replaces the report.

## Scope and Preconditions

Pure serialization + classification. The only import is `sha256_text`; nothing
here reads a file, runs a gate or reads a clock.

## Primary Workflow

A gate renders a receipt (`evidence_receipt_render`) after printing its verdict.
The release census parses it back (`parse_evidence_receipt`) and asks
`receipt_is_fresh` whether it is bound to the artifact and seal currently being
released, within the allowed age, with a PASS verdict.

## Key Concepts

| Concept | Description |
|---------|-------------|
| binding | A receipt is evidence only about the (artifact, seal) pair it names |
| freshness | binding + age + PASS verdict, all three |
| `ReceiptReason` | Closed failure vocabulary; every match over it is exhaustive |

## Related Specifications

- test/01_unit/compiler/common/assurance/unsafe_capabilities_spec.spl

## Evidence and Provenance

The canonical text form is mirrored byte-for-byte by the shell writer
`scripts/check/lib/emit_receipt.shs`; a drift shows up as an `unparseable`
receipt in `check-critical-release-seal.shs`, never as a silent pass.

## Recovery and Troubleshooting

A receipt that does not satisfy an obligation is classified into exactly one
`ReceiptReason`; re-running the producing gate is the fix for every one of them.

## Compatibility and Limitations

`receipt_is_fresh` reads the module clock (`evidence_receipt_set_now`) because
00.common may not import a time module; callers that care about age set it.

## Scenarios

### Evidence receipts

#### round-trips through its canonical text form

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips through its canonical text form
- render a receipt and parse it back
- every field survives, including a verdict line containing '='
   - Expected: back.check_id equals `check-example`
   - Expected: back.artifact_sha256 equals `aaaa`
   - Expected: back.seal_hash equals `bbbb`
   - Expected: back.produced_at equals `1000`
   - Expected: back.verdict_line equals `PASS — 12 thing(s) checked, bad=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips through its canonical text form")
step("render a receipt and parse it back")
val r = sample_receipt()
val parsed = parse_evidence_receipt(evidence_receipt_render(r))
expect(parsed != nil).to_be_true()
step("every field survives, including a verdict line containing '='")
val back: EvidenceReceipt = parsed!
expect(back.check_id).to_equal("check-example")
expect(back.artifact_sha256).to_equal("aaaa")
expect(back.seal_hash).to_equal("bbbb")
expect(back.produced_at).to_equal(1000)
expect(back.verdict_line).to_equal("PASS — 12 thing(s) checked, bad=0")
```

</details>

#### hashes identically for identical content and differently for any change

- hashes identically for identical content and differently for any change
- two receipts with the same fields hash the same
   - Expected: evidence_receipt_hash(sample_receipt()) equals `evidence_receipt_hash(sample_receipt())`
- changing the artifact hash changes the receipt hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes identically for identical content and differently for any change")
step("two receipts with the same fields hash the same")
expect(evidence_receipt_hash(sample_receipt())).to_equal(evidence_receipt_hash(sample_receipt()))
step("changing the artifact hash changes the receipt hash")
var other = sample_receipt()
other.artifact_sha256 = "cccc"
expect(evidence_receipt_hash(other) == evidence_receipt_hash(sample_receipt())).to_be_false()
```

</details>

#### accepts a receipt that is bound, timely and PASSing

- accepts a receipt that is bound, timely and PASSing
- current artifact and seal, produced one minute ago


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a receipt that is bound, timely and PASSing")
step("current artifact and seal, produced one minute ago")
expect(receipt_is_fresh_at(sample_receipt(), "aaaa", "bbbb", 3600, 1060)).to_be_true()
```

</details>

#### classifies a receipt for a different artifact as ArtifactMismatch

- classifies a receipt for a different artifact as ArtifactMismatch
- release a different artifact than the receipt names
   - Expected: receipt_reason_name(why!) equals `artifact-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a receipt for a different artifact as ArtifactMismatch")
step("release a different artifact than the receipt names")
val why = receipt_failure_reason_at(sample_receipt(), "zzzz", "bbbb", 3600, 1060)
expect(why != nil).to_be_true()
expect(receipt_reason_name(why!)).to_equal("artifact-mismatch")
```

</details>

#### classifies a receipt for a different seal as SealMismatch

- classifies a receipt for a different seal as SealMismatch
- same artifact, different seal
   - Expected: receipt_reason_name(why!) equals `seal-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a receipt for a different seal as SealMismatch")
step("same artifact, different seal")
val why = receipt_failure_reason_at(sample_receipt(), "aaaa", "zzzz", 3600, 1060)
expect(receipt_reason_name(why!)).to_equal("seal-mismatch")
```

</details>

#### classifies an old receipt as Stale

- classifies an old receipt as Stale
- produced far outside the allowed age
   - Expected: receipt_reason_name(why!) equals `stale`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies an old receipt as Stale")
step("produced far outside the allowed age")
val why = receipt_failure_reason_at(sample_receipt(), "aaaa", "bbbb", 60, 999999)
expect(receipt_reason_name(why!)).to_equal("stale")
```

</details>

#### classifies a receipt from the future as Stale

- classifies a receipt from the future as Stale
- now is BEFORE the receipt claims to have been produced
   - Expected: receipt_reason_name(why!) equals `stale`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a receipt from the future as Stale")
step("now is BEFORE the receipt claims to have been produced")
val why = receipt_failure_reason_at(sample_receipt(), "aaaa", "bbbb", 60, 1)
expect(receipt_reason_name(why!)).to_equal("stale")
```

</details>

#### classifies a bound, timely FAIL verdict as VerdictNotPass

- classifies a bound, timely FAIL verdict as VerdictNotPass
- a gate that ran and failed still mints a receipt
   - Expected: receipt_reason_name(why!) equals `verdict-not-pass`
- an ERROR verdict is not a pass either


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a bound, timely FAIL verdict as VerdictNotPass")
step("a gate that ran and failed still mints a receipt")
var r = sample_receipt()
r.verdict_line = "FAIL — 12 thing(s) checked, bad=3"
expect(receipt_verdict_is_pass(r)).to_be_false()
val why = receipt_failure_reason_at(r, "aaaa", "bbbb", 3600, 1060)
expect(receipt_reason_name(why!)).to_equal("verdict-not-pass")
step("an ERROR verdict is not a pass either")
r.verdict_line = "ERROR — nothing was checked (no compiler)"
expect(receipt_verdict_is_pass(r)).to_be_false()
```

</details>

#### refuses to parse anything that is not canonical receipt/v1

- refuses to parse anything that is not canonical receipt/v1
- a report is not a receipt
- a wrong magic line is rejected
- a truncated receipt is rejected
- a non-numeric timestamp is rejected, not coerced to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to parse anything that is not canonical receipt/v1")
step("a report is not a receipt")
expect(parse_evidence_receipt("coverage is 100%\n") == nil).to_be_true()
step("a wrong magic line is rejected")
expect(parse_evidence_receipt("receipt/v2\ncheck_id=x\n") == nil).to_be_true()
step("a truncated receipt is rejected")
expect(parse_evidence_receipt("receipt/v1\ncheck_id=x\n") == nil).to_be_true()
step("a non-numeric timestamp is rejected, not coerced to 0")
val bad = "receipt/v1\ncheck_id=x\nartifact_sha256=a\nseal_hash=b\nproduced_at=soon\nproducer_identity=p\nverdict_line=PASS — ok\n"
expect(parse_evidence_receipt(bad) == nil).to_be_true()
```

</details>

#### names every reason in the closed vocabulary exactly once

- names every reason in the closed vocabulary exactly once
- the table is non-vacuous
   - Expected: all_receipt_reasons().len() equals `6`
- no two reasons share a name
   - Expected: names.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names every reason in the closed vocabulary exactly once")
step("the table is non-vacuous")
expect(all_receipt_reasons().len()).to_equal(6)
step("no two reasons share a name")
var names: [text] = []
for reason in all_receipt_reasons():
    val n = receipt_reason_name(reason)
    expect(names.contains(n)).to_be_false()
    names.push(n)
expect(names.len()).to_equal(6)
```

</details>

#### uses the module clock for the plan-named four-argument entry point

- uses the module clock for the plan-named four-argument entry point
- with the clock set inside the window the receipt is fresh
- moving the clock past the window makes the same receipt stale


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the module clock for the plan-named four-argument entry point")
step("with the clock set inside the window the receipt is fresh")
val _ = evidence_receipt_set_now(1060)
expect(receipt_is_fresh(sample_receipt(), "aaaa", "bbbb", 3600)).to_be_true()
step("moving the clock past the window makes the same receipt stale")
val _2 = evidence_receipt_set_now(999999)
expect(receipt_is_fresh(sample_receipt(), "aaaa", "bbbb", 60)).to_be_false()
```

</details>

#### derives the receipt file name from the check id

- derives the receipt file name from the check id
- the census looks a receipt up by check id alone
   - Expected: evidence_receipt_file_name("check-aspect-seal") equals `check-aspect-seal.receipt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the receipt file name from the check id")
step("the census looks a receipt up by check id alone")
expect(evidence_receipt_file_name("check-aspect-seal")).to_equal("check-aspect-seal.receipt")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md §Phase 9`
- **Research:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md §15, §19, §22, §23.9`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa3e7ce87708ff19e5b7e16f2e8b04d453fb3d2a90a4bf5f46a4b59e361c8aa8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa3e7ce87708ff19e5b7e16f2e8b04d453fb3d2a90a4bf5f46a4b59e361c8aa8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa3e7ce87708ff19e5b7e16f2e8b04d453fb3d2a90a4bf5f46a4b59e361c8aa8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/common/assurance/evidence_receipt_spec.spl
mirror: doc/06_spec/unit/compiler/common/assurance/evidence_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/common/assurance/evidence_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/compiler/common/assurance/evidence_receipt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/common/assurance/evidence_receipt_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips through its canonical text form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/assurance/evidence_receipt_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes identically for identical content and differently for any change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/assurance/evidence_receipt_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a receipt that is bound, timely and PASSing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
