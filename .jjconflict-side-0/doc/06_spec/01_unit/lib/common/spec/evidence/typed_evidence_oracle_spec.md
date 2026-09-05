# Modern SSpec typed-evidence oracles

> For QA authors writing modern SSpec scenarios: this spec proves the typed

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Modern SSpec typed-evidence oracles

For QA authors writing modern SSpec scenarios: this spec proves the typed

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

For QA authors writing modern SSpec scenarios: this spec proves the typed
oracle surface itself — selector construction, check kinds, manifest
completeness, and the fail-closed `compare_evidence` verdict plus manual-block
projection. Audience: evidence-lane reviewers who need the comparator's rules
to hold (ignores carry reasons, missing evidence fails, oracles are positive)
before trusting any spec built on top of them.

## Scenarios

### Typed evidence oracles

#### accepts a response whose declared fields all match

- accepts a response whose declared fields all match
- Capture the LIST request and response as canonical evidence
- Compare the capture against the declared protocol oracle
- Verify every declared field passed and the volatile date was ignored
   - Expected: result.status equals `EvidenceStatus.passed`
   - Expected: ignored equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a response whose declared fields all match")
step("Capture the LIST request and response as canonical evidence")
val evidence = list_response_evidence()

step("Compare the capture against the declared protocol oracle")
val result = compare_evidence(evidence, list_response_oracle())

step("Verify every declared field passed and the volatile date was ignored")
expect(result.status).to_equal(EvidenceStatus.passed)
expect(result.summary).to_contain("passed")

var ignored = 0
for check in result.checks:
    if check.status == EvidenceStatus.ignored:
        ignored = ignored + 1
expect(ignored).to_equal(1)
```

</details>

#### reports the failing field when a checked value differs

- reports the failing field when a checked value differs
- Capture a response whose status is 500 instead of 200
- Compare the capture against the same oracle
- Verify the report names the status field and both values
   - Expected: result.status equals `EvidenceStatus.failed`
   - Expected: check.expected equals `200`
   - Expected: check.actual equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the failing field when a checked value differs")
step("Capture a response whose status is 500 instead of 200")
var evidence = list_response_evidence()
evidence.nodes[2] = evidence_node("response.status", "500")

step("Compare the capture against the same oracle")
val result = compare_evidence(evidence, list_response_oracle())

step("Verify the report names the status field and both values")
expect(result.status).to_equal(EvidenceStatus.failed)
var found = false
for check in result.checks:
    if check.selector == "response.status" and check.status == EvidenceStatus.failed:
        found = true
        expect(check.expected).to_equal("200")
        expect(check.actual).to_equal("500")
assert_true(found)
```

</details>

#### rejects a capture that could not be parsed

- rejects a capture that could not be parsed
- Attempt to compare evidence whose grammar did not parse
- Verify the parse error fails the capture instead of yielding an empty pass
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a capture that could not be parsed")
step("Attempt to compare evidence whose grammar did not parse")
val broken = canonical_evidence_parse_error("protocol_text", "simple-list/1", "line 2: expected CRLF")
val result = compare_evidence(broken, list_response_oracle())

step("Verify the parse error fails the capture instead of yielding an empty pass")
expect(result.status).to_equal(EvidenceStatus.failed)
expect(result.summary).to_contain("failed to parse")
```

</details>

#### rejects an oracle that ignores every field

- rejects an oracle that ignores every field
- Declare an oracle whose only checks are ignores
- Compare a healthy capture against it
- Verify the capture fails for asserting nothing about production
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an oracle that ignores every field")
step("Declare an oracle whose only checks are ignores")
val vacuous = oracle_spec(
    "simple-list/1",
    [check_ignore("response.headers.date", "server clock")]
)
assert_false(has_positive_oracle(vacuous))

step("Compare a healthy capture against it")
val result = compare_evidence(list_response_evidence(), vacuous)

step("Verify the capture fails for asserting nothing about production")
expect(result.status).to_equal(EvidenceStatus.failed)
expect(result.summary).to_contain("no positive production check")
```

</details>

#### rejects an ignored value that records no reason

- rejects an ignored value that records no reason
- Declare an ignore with an empty reason
- Verify the comparison fails rather than hiding the unchecked field
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an ignored value that records no reason")
step("Declare an ignore with an empty reason")
val unexplained = oracle_spec(
    "simple-list/1",
    [check_exact("response.status", "200"), check_ignore("response.headers.date", "")]
)
assert_false(ignores_have_reasons(unexplained))

step("Verify the comparison fails rather than hiding the unchecked field")
val result = compare_evidence(list_response_evidence(), unexplained)
expect(result.status).to_equal(EvidenceStatus.failed)
expect(result.summary).to_contain("no recorded reason")
```

</details>

#### rejects a selector that resolves to no field

- rejects a selector that resolves to no field
- Check a field the capture never produced
- Verify the unresolved selector fails instead of checking nothing
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a selector that resolves to no field")
step("Check a field the capture never produced")
val missing = oracle_spec("simple-list/1", [check_exact("response.headers.etag", "abc")])
val result = compare_evidence(list_response_evidence(), missing)

step("Verify the unresolved selector fails instead of checking nothing")
expect(result.status).to_equal(EvidenceStatus.failed)
var reported = false
for check in result.checks:
    if check.selector == "response.headers.etag":
        reported = true
        expect(check.detail).to_contain("resolved no node")
assert_true(reported)
```

</details>

#### rejects a single-value selector that resolves to several fields

- rejects a single-value selector that resolves to several fields
- Check a repeated field with a single-value selector
- Verify the ambiguity fails instead of silently taking the first match
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a single-value selector that resolves to several fields")
step("Check a repeated field with a single-value selector")
val ambiguous = oracle_spec("simple-list/1", [check_exact("response.body.items", "alpha")])
val result = compare_evidence(list_response_evidence(), ambiguous)

step("Verify the ambiguity fails instead of silently taking the first match")
expect(result.status).to_equal(EvidenceStatus.failed)
var reported = false
for check in result.checks:
    if check.selector == "response.body.items":
        reported = true
        expect(check.detail).to_contain("resolved 2 nodes")
assert_true(reported)
```

</details>

#### rejects an undeclared field under a closed oracle

- rejects an undeclared field under a closed oracle
- Add a field the oracle never mentions
- Compare under the closed protocol oracle
- Verify the undeclared field fails the capture
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an undeclared field under a closed oracle")
step("Add a field the oracle never mentions")
var evidence = list_response_evidence()
evidence.nodes.push(evidence_node("response.headers.x-debug", "internal"))

step("Compare under the closed protocol oracle")
val result = compare_evidence(evidence, list_response_oracle())

step("Verify the undeclared field fails the capture")
expect(result.status).to_equal(EvidenceStatus.failed)
var reported = false
for check in result.checks:
    if check.selector == "response.headers.x-debug":
        reported = true
        expect(check.detail).to_contain("undeclared field")
assert_true(reported)
```

</details>

#### accepts an undeclared field only when the oracle is explicitly open

- accepts an undeclared field only when the oracle is explicitly open
- Declare the same checks with an open document policy
- Verify the extra field is tolerated when openness was chosen deliberately
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts an undeclared field only when the oracle is explicitly open")
step("Declare the same checks with an open document policy")
var evidence = list_response_evidence()
evidence.nodes.push(evidence_node("response.headers.x-debug", "internal"))
val base = list_response_oracle()
val open_spec = oracle_spec_open("simple-list/1", base.checks)

step("Verify the extra field is tolerated when openness was chosen deliberately")
val result = compare_evidence(evidence, open_spec)
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

#### fails a correlation check when the two identifiers differ

- fails a correlation check when the two identifiers differ
- Capture a response echoing a different correlation identifier
- Verify the correlation mismatch is reported
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails a correlation check when the two identifiers differ")
step("Capture a response echoing a different correlation identifier")
var evidence = list_response_evidence()
evidence.nodes[5] = evidence_node("response.headers.correlation-id", "0000000000000000")

step("Verify the correlation mismatch is reported")
val result = compare_evidence(evidence, list_response_oracle())
expect(result.status).to_equal(EvidenceStatus.failed)
var reported = false
for check in result.checks:
    if check.selector == "response.headers.correlation-id" and check.status == EvidenceStatus.failed:
        reported = true
        expect(check.detail).to_contain("correlation mismatch")
assert_true(reported)
```

</details>

### Anchored pattern classes

#### matches a value of exactly the declared class and length

- Match exact-length values of each declared pattern class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-001
step("Match exact-length values of each declared pattern class")
assert_true(pattern_matches("hex:16", "4C73A91801D58F22"))
assert_true(pattern_matches("digit:3", "200"))
assert_true(pattern_matches("alnum:*", "alpha7"))
```

</details>

#### rejects a value that is longer than the declared length

- Match a hex value two characters longer than declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-001
step("Match a hex value two characters longer than declared")
assert_false(pattern_matches("hex:16", "4C73A91801D58F22EE"))
```

</details>

#### rejects a value that only contains the declared shape

- Match a value with the declared shape embedded in other text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-001
step("Match a value with the declared shape embedded in other text")
assert_false(pattern_matches("hex:16", "id=4C73A91801D58F22"))
```

</details>

#### rejects an empty value and an unknown class

- Match an empty value, then a value of an undeclared class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-001
step("Match an empty value, then a value of an undeclared class")
assert_false(pattern_matches("hex:16", ""))
assert_false(pattern_matches("base64:8", "AAAAAAAA"))
```

</details>

### Multiplicity and order oracles

#### accepts an unordered match when order is insignificant

- accepts an unordered match when order is insignificant
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts an unordered match when order is insignificant")
val result = compare_evidence(
    items(["beta", "alpha"]),
    oracle_spec("items/1", [check_multiset("items", ["alpha", "beta"])])
)
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

#### rejects a duplicated entry that a set comparison would accept

- rejects a duplicated entry that a set comparison would accept
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a duplicated entry that a set comparison would accept")
val result = compare_evidence(
    items(["alpha", "alpha"]),
    oracle_spec("items/1", [check_multiset("items", ["alpha", "beta"])])
)
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

#### rejects reordered entries when order is part of the contract

- rejects reordered entries when order is part of the contract
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects reordered entries when order is part of the contract")
val result = compare_evidence(
    items(["beta", "alpha"]),
    oracle_spec("items/1", [check_ordered("items", ["alpha", "beta"])])
)
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

### Numeric tolerance oracles

#### accepts a measurement inside the declared tolerance

- accepts a measurement inside the declared tolerance
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a measurement inside the declared tolerance")
val result = compare_evidence(
    sample("1503"),
    oracle_spec("throughput/1", [check_numeric_tolerance("rps", "1500", 10, "warm-cache jitter")])
)
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

#### rejects a measurement outside the declared tolerance

- rejects a measurement outside the declared tolerance
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a measurement outside the declared tolerance")
val result = compare_evidence(
    sample("1400"),
    oracle_spec("throughput/1", [check_numeric_tolerance("rps", "1500", 10, "warm-cache jitter")])
)
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

### Evidence manifest provenance

#### accepts a manifest that names its spec, provider, run and artifacts

- accepts a manifest that names its spec, provider, run and artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a manifest that names its spec, provider, run and artifacts")
assert_true(evidence_manifest_is_complete(complete_manifest()))
```

</details>

#### rejects a manifest with no artifact hash

- rejects a manifest with no artifact hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a manifest with no artifact hash")
var manifest = complete_manifest()
manifest.artifact_sha256 = ""
assert_false(evidence_manifest_is_complete(manifest))
```

</details>

#### rejects a manifest with no spec hash

- rejects a manifest with no spec hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a manifest with no spec hash")
var manifest = complete_manifest()
manifest.spec_sha256 = ""
assert_false(evidence_manifest_is_complete(manifest))
```

</details>

#### serializes fields in a fixed order so two runs diff meaningfully

- serializes fields in a fixed order so two runs diff meaningfully
   - Expected: lines.len() equals `11`
   - Expected: lines[0] equals `schema: simple.sspec.evidence.v1`
   - Expected: lines[10] equals `status: PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes fields in a fixed order so two runs diff meaningfully")
val lines = evidence_manifest_lines(complete_manifest())
expect(lines.len()).to_equal(11)
expect(lines[0]).to_equal("schema: simple.sspec.evidence.v1")
expect(lines[10]).to_equal("status: PASS")
```

</details>

### Manual projection

#### projects a comparison into an expected/actual block and a verdict

- projects a comparison into an expected/actual block and a verdict
   - Expected: blocks.len() equals `2`
   - Expected: manual_block_kind_name(blocks[0].kind) equals `expected_actual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects a comparison into an expected/actual block and a verdict")
val result = compare_evidence(list_response_evidence(), list_response_oracle())
val blocks = comparison_to_manual_blocks("List projects", result)

expect(blocks.len()).to_equal(2)
expect(manual_block_kind_name(blocks[0].kind)).to_equal("expected_actual")
expect(blocks[0].lines[0]).to_contain("Selector")
expect(blocks[1].lines[0]).to_contain("PASS")
```

</details>

### Red-team hardening of the evaluator

#### rejects an oracle built only from correlation binds

- rejects an oracle built only from correlation binds
- Declare an oracle whose only non-ignore check merely captures a value
- Verify a bind alone does not count as a positive production check
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an oracle built only from correlation binds")
step("Declare an oracle whose only non-ignore check merely captures a value")
val bind_only = oracle_spec(
    "simple-list/1",
    [
        check_bind("request.headers.correlation-id", "request_id"),
        check_ignore("response.headers.date", "server clock")
    ]
)

step("Verify a bind alone does not count as a positive production check")
assert_false(has_positive_oracle(bind_only))
val result = compare_evidence(list_response_evidence(), bind_only)
expect(result.status).to_equal(EvidenceStatus.failed)
expect(result.summary).to_contain("no positive production check")
```

</details>

#### rejects a tolerance comparison between values that are not numbers

- rejects a tolerance comparison between values that are not numbers
- Compare two unrelated words under a numeric tolerance oracle
- Verify neither value is silently read as zero
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a tolerance comparison between values that are not numbers")
step("Compare two unrelated words under a numeric tolerance oracle")
val evidence = canonical_evidence("statistics", "throughput/1", [evidence_node("rps", "banana")])
val result = compare_evidence(
    evidence,
    oracle_spec("throughput/1", [check_numeric_tolerance("rps", "elephant", 0, "measured jitter")])
)

step("Verify neither value is silently read as zero")
expect(result.status).to_equal(EvidenceStatus.failed)
var reported = false
for check in result.checks:
    if check.selector == "rps":
        reported = true
        expect(check.detail).to_contain("not numeric")
assert_true(reported)
```

</details>

#### rejects a tolerance comparison whose difference would overflow

- rejects a tolerance comparison whose difference would overflow
- Compare the largest and smallest representable measurements
- Verify the widest possible disagreement does not wrap into a pass
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a tolerance comparison whose difference would overflow")
step("Compare the largest and smallest representable measurements")
val evidence = canonical_evidence(
    "statistics",
    "throughput/1",
    [evidence_node("rps", "-9223372036854775807")]
)
val result = compare_evidence(
    evidence,
    oracle_spec("throughput/1", [check_numeric_tolerance("rps", "9223372036854775807", 1, "measured jitter")])
)

step("Verify the widest possible disagreement does not wrap into a pass")
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

#### rejects a manifest whose digests are not digests

- rejects a manifest whose digests are not digests
- Record provenance with placeholder text where hashes belong
- Verify the receipt is refused because it identifies nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a manifest whose digests are not digests")
step("Record provenance with placeholder text where hashes belong")
var manifest = evidence_manifest(
    "list-projects",
    "simple-list/1",
    "test/03_system/tools/spipe/examples/text_protocol_manual_spec.spl",
    "z",
    "protocol_trace_provider",
    "1",
    "run-2026-08-08-01",
    "linux-x86_64",
    "not-a-hash",
    EvidenceStatus.passed
)

step("Verify the receipt is refused because it identifies nothing")
assert_false(evidence_manifest_is_complete(manifest))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-SSPEC-EVD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e011eb5a08a471b72f1e4107ce0bb8ea27a6f853eebb05718fb543e4e3954628`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e011eb5a08a471b72f1e4107ce0bb8ea27a6f853eebb05718fb543e4e3954628`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e011eb5a08a471b72f1e4107ce0bb8ea27a6f853eebb05718fb543e4e3954628`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches a value of exactly the declared class and length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl:259:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a value that is longer than the declared length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl:264:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a value that only contains the declared shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
