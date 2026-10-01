# global_array_push_linear_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# global_array_push_linear_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### module-global array push from a helper fn

#### keeps value semantics: an alias taken before a push does not see it

- Verify: keeps value semantics: an alias taken before a push does not see it
   - Expected: before.len() equals `1`
   - Expected: g_tag.len() equals `3`
   - Expected: g_tag[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps value semantics: an alias taken before a push does not see it")
# @req: REQ-SSPEC-LOCAL-001
reset()
add(1)
val before = snapshot()
add(2)
add(3)
expect(before.len()).to_equal(1)
expect(g_tag.len()).to_equal(3)
expect(g_tag[2]).to_equal(3)
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
time_fill(2000)
val small = time_fill(5000)
val large = time_fill(20000)
val floor = if small < 20000: 20000 else: small
expect(large <= floor * 8).to_be_true()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c639dfd611e3d0de4af8a04a3de70efd6a30dc45e13ce348445a8327f037ad37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c639dfd611e3d0de4af8a04a3de70efd6a30dc45e13ce348445a8327f037ad37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c639dfd611e3d0de4af8a04a3de70efd6a30dc45e13ce348445a8327f037ad37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/global_array_push_linear_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/global_array_push_linear_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/global_array_push_linear_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps value semantics: an alias taken before a push does not see it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '4x the pushes cost less than 8x the time (linear, not quadratic)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl. -->
