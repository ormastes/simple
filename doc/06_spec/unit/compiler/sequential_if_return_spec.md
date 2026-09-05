# sequential_if_return_spec

> Purpose: Prove that sequential if return.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sequential_if_return_spec

Purpose: Prove that sequential if return.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/sequential_if_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that sequential if return.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### sequential if return

#### first branch works

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- first branch works
- Verify: first branch works
   - Expected: classify(1) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first branch works")
step("Verify: first branch works")
# @req: REQ-COMP-SEQUENTIAL-IF-RETURN-001
expect(classify(1)).to_equal(10)
```

</details>

#### second branch works

- second branch works
- Verify: second branch works
   - Expected: classify(2) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second branch works")
step("Verify: second branch works")
expect(classify(2)).to_equal(20)
```

</details>

#### third branch works

- third branch works
- Verify: third branch works
   - Expected: classify(3) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("third branch works")
step("Verify: third branch works")
expect(classify(3)).to_equal(30)
```

</details>

#### default fallthrough

- default fallthrough
- Verify: default fallthrough
   - Expected: classify(99) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default fallthrough")
step("Verify: default fallthrough")
expect(classify(99)).to_equal(-1)
```

</details>

#### u8 first branch

- u8 first branch
- Verify: u8 first branch
   - Expected: classify_u8(0x41u8) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("u8 first branch")
step("Verify: u8 first branch")
expect(classify_u8(0x41u8)).to_equal(0)
```

</details>

#### u8 second branch

- u8 second branch
- Verify: u8 second branch
   - Expected: classify_u8(0x42u8) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("u8 second branch")
step("Verify: u8 second branch")
expect(classify_u8(0x42u8)).to_equal(1)
```

</details>

#### u8 third branch

- u8 third branch
- Verify: u8 third branch
   - Expected: classify_u8(0x43u8) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("u8 third branch")
step("Verify: u8 third branch")
expect(classify_u8(0x43u8)).to_equal(2)
```

</details>

#### u8 default

- u8 default
- Verify: u8 default
   - Expected: classify_u8(0x44u8) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("u8 default")
step("Verify: u8 default")
expect(classify_u8(0x44u8)).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-SEQUENTIAL-IF-RETURN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8d4d218d9f8be417b8bb70e34504b90aa6cbfd3ecabb475464aac3977fff412`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8d4d218d9f8be417b8bb70e34504b90aa6cbfd3ecabb475464aac3977fff412`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8d4d218d9f8be417b8bb70e34504b90aa6cbfd3ecabb475464aac3977fff412`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/sequential_if_return_spec.spl
mirror: doc/06_spec/unit/compiler/sequential_if_return_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/sequential_if_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/sequential_if_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/sequential_if_return_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/sequential_if_return_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'first branch works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/sequential_if_return_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'second branch works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/sequential_if_return_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'third branch works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
