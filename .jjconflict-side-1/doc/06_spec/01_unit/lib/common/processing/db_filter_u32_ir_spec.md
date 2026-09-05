# db_filter_u32_ir_spec

> Verify the shared data-bearing DB filter IR and independent CPU oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# db_filter_u32_ir_spec

Verify the shared data-bearing DB filter IR and independent CPU oracle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verify the shared data-bearing DB filter IR and independent CPU oracle.

## Scenarios

### DB scan/filter ProcessingIR

#### should preserve unsigned boundary semantics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve unsigned boundary semantics
   - Expected: processing_db_filter_u32_cpu_row_ids(ir) equals `[0, 1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve unsigned boundary semantics")
val ir = processing_ir_db_filter_u32(
    [0u32, 1u32, 0xfffffffeu32, 0xffffffffu32],
    0u32, 0xffffffffu32)
expect(processing_db_filter_u32_cpu_mask(ir)).to_equal(
    [1u32, 1u32, 1u32, 1u32])
expect(processing_db_filter_u32_cpu_row_ids(ir)).to_equal([0, 1, 2, 3])
```

</details>

#### should filter four thousand patterned rows exactly

- should filter four thousand patterned rows exactly
   - Expected: mask.len() equals `4096`
   - Expected: rows.len() equals `2048`
   - Expected: rows[0] equals `64`
   - Expected: rows[2047] equals `4031`
   - Expected: mask[63] equals `0u32`
   - Expected: mask[64] equals `1u32`
   - Expected: mask[191] equals `1u32`
   - Expected: mask[192] equals `0u32`
   - Expected: processing_db_filter_u32_mismatch_count(mask, mask) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should filter four thousand patterned rows exactly")
var values: [u32] = []
var index: i64 = 0
while index < 4096:
    values.push((index % 256).to_u32())
    index = index + 1
val ir = processing_ir_db_filter_u32(values, 64u32, 191u32)
val mask = processing_db_filter_u32_cpu_mask(ir)
val rows = processing_db_filter_u32_row_ids(ir, mask)
expect(mask.len()).to_equal(4096)
expect(rows.len()).to_equal(2048)
expect(rows[0]).to_equal(64)
expect(rows[2047]).to_equal(4031)
expect(mask[63]).to_equal(0u32)
expect(mask[64]).to_equal(1u32)
expect(mask[191]).to_equal(1u32)
expect(mask[192]).to_equal(0u32)
expect(processing_db_filter_u32_mismatch_count(mask, mask)).to_equal(0)
```

</details>

#### should produce an exact inclusive filter mask and projected row IDs

- should produce an exact inclusive filter mask and projected row IDs
- Build a data-bearing DB filter batch
- Execute the independent CPU oracle
   - Expected: mask equals `[0u32, 1u32, 1u32, 1u32, 0u32]`
   - Expected: processing_db_filter_u32_cpu_row_ids(ir) equals `[1, 2, 3]`
   - Expected: processing_db_filter_u32_mask_checksum(mask) equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should produce an exact inclusive filter mask and projected row IDs")
step("Build a data-bearing DB filter batch")
val ir = processing_ir_db_filter_u32(
    [2u32, 7u32, 9u32, 10u32, 15u32], 7u32, 10u32)

step("Execute the independent CPU oracle")
val mask = processing_db_filter_u32_cpu_mask(ir)
expect(mask).to_equal([0u32, 1u32, 1u32, 1u32, 0u32])
expect(processing_db_filter_u32_cpu_row_ids(ir)).to_equal([1, 2, 3])
expect(processing_db_filter_u32_mask_checksum(mask)).to_equal(25)
```

</details>

#### should reject empty input inverted ranges and malformed device masks

- should reject empty input inverted ranges and malformed device masks
- Construct invalid filter batches
- Require typed validation failures
   - Expected: processing_db_filter_u32_validate(empty).reason equals `db-filter-input-empty`
   - Expected: processing_db_filter_u32_validate(inverted).reason equals `db-filter-range-invalid`
- Reject device masks with the wrong length or non-binary values
   - Expected: processing_db_filter_u32_row_ids(valid, [1u32]) equals `[]`
   - Expected: processing_db_filter_u32_row_ids(valid, [1u32, 2u32]) equals `[]`
   - Expected: processing_db_filter_u32_mismatch_count([1u32, 0u32], [1u32]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject empty input inverted ranges and malformed device masks")
step("Construct invalid filter batches")
val empty = processing_ir_db_filter_u32([], 1u32, 2u32)
val inverted = processing_ir_db_filter_u32([1u32], 2u32, 1u32)

step("Require typed validation failures")
expect(processing_db_filter_u32_validate(empty).reason).to_equal("db-filter-input-empty")
expect(processing_db_filter_u32_validate(inverted).reason).to_equal("db-filter-range-invalid")

step("Reject device masks with the wrong length or non-binary values")
val valid = processing_ir_db_filter_u32([1u32, 2u32], 1u32, 2u32)
expect(processing_db_filter_u32_row_ids(valid, [1u32])).to_equal([])
expect(processing_db_filter_u32_row_ids(valid, [1u32, 2u32])).to_equal([])
expect(processing_db_filter_u32_mismatch_count([1u32, 0u32], [1u32])).to_equal(2)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68f37415c48b18f3193896138e567ead4e24219c09f996ff0aa010f4c3770240`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68f37415c48b18f3193896138e567ead4e24219c09f996ff0aa010f4c3770240`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68f37415c48b18f3193896138e567ead4e24219c09f996ff0aa010f4c3770240`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl
mirror: doc/06_spec/01_unit/lib/common/processing/db_filter_u32_ir_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/processing/db_filter_u32_ir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/processing/db_filter_u32_ir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve unsigned boundary semantics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve unsigned boundary semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filter four thousand patterned rows exactly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should filter four thousand patterned rows exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should produce an exact inclusive filter mask and projected row IDs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should produce an exact inclusive filter mask and projected row IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/db_filter_u32_ir_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject empty input inverted ranges and malformed device masks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
