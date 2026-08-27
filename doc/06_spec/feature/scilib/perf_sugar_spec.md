# perf_sugar_spec

> Purpose: Verify perf_sugar typed array allocation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# perf_sugar_spec

Purpose: Verify perf_sugar typed array allocation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/perf_sugar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify perf_sugar typed array allocation.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### perf_sugar typed array allocation

#### f64 zeros creates correct length

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- f64 zeros creates correct length
- f64 zeros creates correct length
   - Expected: buf.size() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("f64 zeros creates correct length")
step("f64 zeros creates correct length")
# @req: REQ-FEAT-SCILIB-PERF-SUGAR-SPEC-001
val buf = TypedBuffer.zeros(8)
expect(buf.size()).to_equal(8)
```

</details>

#### f64 zeros fills with zero

- f64 zeros fills with zero
- f64 zeros fills with zero
   - Expected: buf.get(0) equals `0.0`
   - Expected: buf.get(3) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("f64 zeros fills with zero")
step("f64 zeros fills with zero")
val buf = TypedBuffer.zeros(4)
expect(buf.get(0)).to_equal(0.0)
expect(buf.get(3)).to_equal(0.0)
```

</details>

#### f64 fill creates uniform buffer

- f64 fill creates uniform buffer
- f64 fill creates uniform buffer
   - Expected: buf.size() equals `5`
   - Expected: buf.get(0) equals `3.14`
   - Expected: buf.get(4) equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("f64 fill creates uniform buffer")
step("f64 fill creates uniform buffer")
val buf = TypedBuffer.fill(5, 3.14)
expect(buf.size()).to_equal(5)
expect(buf.get(0)).to_equal(3.14)
expect(buf.get(4)).to_equal(3.14)
```

</details>

#### int zeros creates correct length

- int zeros creates correct length
- int zeros creates correct length
   - Expected: buf.size() equals `6`
   - Expected: buf.get(0) equals `0`
   - Expected: buf.get(5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("int zeros creates correct length")
step("int zeros creates correct length")
val buf = IntBuffer.zeros(6)
expect(buf.size()).to_equal(6)
expect(buf.get(0)).to_equal(0)
expect(buf.get(5)).to_equal(0)
```

</details>

#### byte alloc via rt_bytes_alloc

- byte alloc via rt_bytes_alloc
- byte alloc via rt_bytes_alloc
   - Expected: buf.size() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("byte alloc via rt_bytes_alloc")
step("byte alloc via rt_bytes_alloc")
val buf = ByteBuffer.alloc(16)
expect(buf.size()).to_equal(16)
```

</details>

#### empty buffer has zero length

- empty buffer has zero length
- empty buffer has zero length
   - Expected: buf.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty buffer has zero length")
step("empty buffer has zero length")
val buf = TypedBuffer.zeros(0)
expect(buf.size()).to_equal(0)
```

</details>

#### single element buffer

- single element buffer
- single element buffer
   - Expected: buf.size() equals `1`
   - Expected: buf.get(0) equals `42.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("single element buffer")
step("single element buffer")
val buf = TypedBuffer.fill(1, 42.0)
expect(buf.size()).to_equal(1)
expect(buf.get(0)).to_equal(42.0)
```

</details>

#### int buffer preserves values

- int buffer preserves values
- int buffer preserves values
   - Expected: buf.get(0) equals `0`
   - Expected: buf.get(1) equals `0`
   - Expected: buf.get(2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("int buffer preserves values")
step("int buffer preserves values")
val buf = IntBuffer.zeros(3)
expect(buf.get(0)).to_equal(0)
expect(buf.get(1)).to_equal(0)
expect(buf.get(2)).to_equal(0)
```

</details>

#### moderate size allocation

- moderate size allocation
- moderate size allocation
   - Expected: buf.size() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("moderate size allocation")
step("moderate size allocation")
val buf = TypedBuffer.zeros(100)
expect(buf.size()).to_equal(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-SCILIB-PERF-SUGAR-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fddc990f7caab607c182a7b876aedb5a2e893c4c3f0ad0bf4920b9010ead3fc7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fddc990f7caab607c182a7b876aedb5a2e893c4c3f0ad0bf4920b9010ead3fc7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fddc990f7caab607c182a7b876aedb5a2e893c4c3f0ad0bf4920b9010ead3fc7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/perf_sugar_spec.spl
mirror: doc/06_spec/feature/scilib/perf_sugar_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/perf_sugar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/perf_sugar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/perf_sugar_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/perf_sugar_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f64 zeros creates correct length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/perf_sugar_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f64 zeros fills with zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/perf_sugar_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f64 fill creates uniform buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
