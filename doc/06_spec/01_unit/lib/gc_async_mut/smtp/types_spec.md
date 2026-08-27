# types_spec

> Purpose: Prove that SMTP response parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# types_spec

Purpose: Prove that SMTP response parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/smtp/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SMTP response parsing.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### SMTP response parsing

#### parses numeric response code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses numeric response code
- Verify: parses numeric response code
   - Expected: response_parse_code("250 OK") equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses numeric response code")
step("Verify: parses numeric response code")
# @req: REQ-LIB-GC-ASYNC-MUT-001
expect(response_parse_code("250 OK")).to_equal(250)
```

</details>

#### returns zero for short response code

- returns zero for short response code
- Verify: returns zero for short response code
   - Expected: response_parse_code("25") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero for short response code")
step("Verify: returns zero for short response code")
expect(response_parse_code("25")).to_equal(0)
```

</details>

#### returns zero for malformed response code

- returns zero for malformed response code
- Verify: returns zero for malformed response code
   - Expected: response_parse_code("2x0 bad") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero for malformed response code")
step("Verify: returns zero for malformed response code")
expect(response_parse_code("2x0 bad")).to_equal(0)
```

</details>

#### parses response message

- parses response message
- Verify: parses response message
   - Expected: response_parse_message("250 OK") equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses response message")
step("Verify: parses response message")
expect(response_parse_message("250 OK")).to_equal("OK")
```

</details>

#### detects multiline response marker

- detects multiline response marker
- Verify: detects multiline response marker
   - Expected: response_is_multiline("250-hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects multiline response marker")
step("Verify: detects multiline response marker")
expect(response_is_multiline("250-hello")).to_equal(true)
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

- `REQ-SSPEC-LIB`
- `REQ-LIB-GC-ASYNC-MUT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c436def72692fffa90cc5cfd66f1b6796a912a543b132fb6716a3d5ab4833948`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c436def72692fffa90cc5cfd66f1b6796a912a543b132fb6716a3d5ab4833948`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c436def72692fffa90cc5cfd66f1b6796a912a543b132fb6716a3d5ab4833948`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/smtp/types_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/smtp/types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/smtp/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/smtp/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/smtp/types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/smtp/types_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses numeric response code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/smtp/types_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero for short response code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/smtp/types_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero for malformed response code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
