# receiver_hop_depth_linear_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# receiver_hop_depth_linear_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### me-method field push through parameter hops

#### keeps value semantics: an alias taken before the pushes does not see them

- Verify: keeps value semantics: an alias taken before the pushes does not see them
   - Expected: counts[0] equals `1`
   - Expected: counts[1] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps value semantics: an alias taken before the pushes does not see them")
val counts = alias_keeps_snapshot()
expect(counts[0]).to_equal(1)
expect(counts[1]).to_equal(3)
```

</details>

#### propagates every push back to the owning frame, in order

- Verify: propagates every push back to the owning frame, in order
   - Expected: parts.len() equals `4`
   - Expected: parts[0] equals `1`
   - Expected: parts[3] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: propagates every push back to the owning frame, in order")
val parts = order_across_hops()
expect(parts.len()).to_equal(4)
expect(parts[0]).to_equal("1")
expect(parts[3]).to_equal("4")
```

</details>

#### 4x the pushes cost less than 8x the time (linear, not quadratic)

- Verify: 4x the pushes cost less than 8x the time (linear, not quadratic)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: 4x the pushes cost less than 8x the time (linear, not quadratic)")
time_hops(2000)
val small = time_hops(5000)
val large = time_hops(20000)
val floor = if small < 20000: 20000 else: small
expect(large <= floor * 8).to_be_true()
```

</details>

#### three parameter hops cost no more than 8x the direct receiver

- Verify: three parameter hops cost no more than 8x the direct receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: three parameter hops cost no more than 8x the direct receiver")
# @req: REQ-SSPEC-LOCAL-001
time_direct(2000)
val direct = time_direct(10000)
val hopped = time_hops(10000)
val floor = if direct < 20000: 20000 else: direct
expect(hopped <= floor * 8).to_be_true()
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fe0121bd4d3d059c02d0877e734985dd296a50ab6e2fc719b555dd139a946f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fe0121bd4d3d059c02d0877e734985dd296a50ab6e2fc719b555dd139a946f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fe0121bd4d3d059c02d0877e734985dd296a50ab6e2fc719b555dd139a946f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps value semantics: an alias taken before the pushes does not see them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates every push back to the owning frame, in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '4x the pushes cost less than 8x the time (linear, not quadratic)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/interpreter/receiver_hop_depth_linear_spec.spl. -->
