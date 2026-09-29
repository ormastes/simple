# SFFI `[u8]` Return Marshalling — Defect-Class Sweep

> Purpose: Prove that SFFI [u8] return marshalling — defect class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI `[u8]` Return Marshalling — Defect-Class Sweep

Purpose: Prove that SFFI [u8] return marshalling — defect class.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/sffi_byte_array_return_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SFFI [u8] return marshalling — defect class.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### SFFI [u8] return marshalling — defect class

#### positive control: rt_bytes_alloc(24) transports a real 24-byte array

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive control: rt_bytes_alloc(24) transports a real 24-byte array
- Verify: positive control: rt_bytes_alloc(24) transports a real 24-byte array
   - Expected: buf.len() equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("positive control: rt_bytes_alloc(24) transports a real 24-byte array")
step("Verify: positive control: rt_bytes_alloc(24) transports a real 24-byte array")
# @req: REQ-COMP-SFFI-U8-RETURN-MARSHALLING-DEFECT-CLASS-001
val buf = rt_bytes_alloc(24)
expect(buf.len()).to_equal(24)
```

</details>

#### positive control: rt_bytes_alloc(1) is length 1, not a constant

- positive control: rt_bytes_alloc(1) is length 1, not a constant
- Verify: positive control: rt_bytes_alloc(1) is length 1, not a constant
   - Expected: buf.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("positive control: rt_bytes_alloc(1) is length 1, not a constant")
step("Verify: positive control: rt_bytes_alloc(1) is length 1, not a constant")
val buf = rt_bytes_alloc(1)
expect(buf.len()).to_equal(1)
```

</details>

#### rt_byte_array_new declared -> [u8] binds an array

- rt_byte_array_new declared -> [u8] binds an array
- Verify: rt_byte_array_new declared -> [u8] binds an array
   - Expected: buf.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_byte_array_new declared -> [u8] binds an array")
step("Verify: rt_byte_array_new declared -> [u8] binds an array")
val buf = rt_byte_array_new(8)
expect(buf.len() >= 0).to_equal(true)
```

</details>

#### rt_bytes_from_raw(0, 0) declared -> [u8] binds an empty array

- rt_bytes_from_raw(0, 0) declared -> [u8] binds an empty array
- Verify: rt_bytes_from_raw(0, 0) declared -> [u8] binds an empty array
   - Expected: buf.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_bytes_from_raw(0, 0) declared -> [u8] binds an empty array")
step("Verify: rt_bytes_from_raw(0, 0) declared -> [u8] binds an empty array")
val buf = rt_bytes_from_raw(0, 0)
expect(buf.len()).to_equal(0)
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-SFFI-U8-RETURN-MARSHALLING-DEFECT-CLASS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5b0ef2a049ca0804bee40d1d2865c4781c28c9c362ac331c5c12f9ad5abd77e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5b0ef2a049ca0804bee40d1d2865c4781c28c9c362ac331c5c12f9ad5abd77e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5b0ef2a049ca0804bee40d1d2865c4781c28c9c362ac331c5c12f9ad5abd77e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/sffi_byte_array_return_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/sffi_byte_array_return_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/sffi_byte_array_return_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/sffi_byte_array_return_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/sffi_byte_array_return_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/sffi_byte_array_return_class_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: rt_bytes_alloc(24) transports a real 24-byte array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/sffi_byte_array_return_class_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: rt_bytes_alloc(1) is length 1, not a constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/sffi_byte_array_return_class_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_byte_array_new declared -> [u8] binds an array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
