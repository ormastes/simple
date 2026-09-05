# processing_ir_spec

> ProcessingIR validates and executes the portable FillU32 CPU oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_ir_spec

ProcessingIR validates and executes the portable FillU32 CPU oracle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/processing/processing_ir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

ProcessingIR validates and executes the portable FillU32 CPU oracle.

## Scenarios

### ProcessingIR FillU32

#### produces the exact portable CPU oracle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces the exact portable CPU oracle
- Build and validate one FillU32 operation
   - Expected: processing_ir_validate(ir).reason equals `ok`
- Execute the CPU oracle
   - Expected: output.len() equals `3`
   - Expected: output[0] equals `7u32`
   - Expected: output[1] equals `7u32`
   - Expected: output[2] equals `7u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the exact portable CPU oracle")
step("Build and validate one FillU32 operation")
val ir = processing_ir_fill_u32(3, 7u32)
expect(processing_ir_validate(ir).reason).to_equal("ok")

step("Execute the CPU oracle")
val output = processing_ir_cpu_execute(ir)
expect(output.len()).to_equal(3)
expect(output[0]).to_equal(7u32)
expect(output[1]).to_equal(7u32)
expect(output[2]).to_equal(7u32)
```

</details>

#### rejects invalid and overflowing output sizes

- rejects invalid and overflowing output sizes
- Reject zero elements
   - Expected: processing_ir_validate(processing_ir_fill_u32(0, 7u32)).reason equals `invalid-element-count`
- Reject output sizes that overflow the bounded byte count
   - Expected: processing_ir_validate(processing_ir_fill_u32(536870912, 7u32)).reason equals `output-size-overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid and overflowing output sizes")
step("Reject zero elements")
expect(processing_ir_validate(processing_ir_fill_u32(0, 7u32)).reason).to_equal("invalid-element-count")

step("Reject output sizes that overflow the bounded byte count")
expect(processing_ir_validate(processing_ir_fill_u32(536870912, 7u32)).reason).to_equal("output-size-overflow")
```

</details>

#### validates device output without allocating a CPU mirror

- validates device output without allocating a CPU mirror
   - Expected: processing_ir_output_matches(ir, [7u32, 7u32, 7u32]) is true
   - Expected: processing_ir_output_matches(ir, [7u32, 8u32, 7u32]) is false
   - Expected: processing_ir_output_matches(ir, [7u32, 7u32]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates device output without allocating a CPU mirror")
val ir = processing_ir_fill_u32(3, 7u32)
expect(processing_ir_output_matches(ir, [7u32, 7u32, 7u32])).to_equal(true)
expect(processing_ir_output_matches(ir, [7u32, 8u32, 7u32])).to_equal(false)
expect(processing_ir_output_matches(ir, [7u32, 7u32])).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-007`
- `REQ-008`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `311c938d601ad731606262d5cbdb0b2dcc7a6f1d5f5c0e01fbde267212020de8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `311c938d601ad731606262d5cbdb0b2dcc7a6f1d5f5c0e01fbde267212020de8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `311c938d601ad731606262d5cbdb0b2dcc7a6f1d5f5c0e01fbde267212020de8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/processing/processing_ir_spec.spl
mirror: doc/06_spec/01_unit/lib/common/processing/processing_ir_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/processing/processing_ir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/processing/processing_ir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/processing/processing_ir_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/processing/processing_ir_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/processing/processing_ir_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the exact portable CPU oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/processing_ir_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid and overflowing output sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/processing_ir_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates device output without allocating a CPU mirror' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
