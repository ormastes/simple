# Hir Verification Contract Preservation Specification

> Tests covering HIR verification contract preservation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Verification Contract Preservation Specification

## Scenarios

### HIR verification contract preservation

#### keeps the ordinary constructor path explicitly contract-free

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the ordinary constructor path explicitly contract-free
- Construct an ordinary function with the canonical nil field
   - Expected: ordinary.verification_contract.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the ordinary constructor path explicitly contract-free")
step("Construct an ordinary function with the canonical nil field")
val ordinary = hir_function("ordinary", nil)
expect(ordinary.verification_contract.?).to_equal(false)
```

</details>

#### preserves a non-nil contract through semantic resolution

- preserves a non-nil contract through semantic resolution
- Resolve a function without dropping its typed contract model
   - Expected: resolved.verification_contract.? is true
   - Expected: retained.clauses.len() equals `1`
   - Expected: retained.proof_uses equals `ContractProof.valid`
   - Expected: retained.outcome == HirContractOutcome.Plain is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves a non-nil contract through semantic resolution")
step("Resolve a function without dropping its typed contract model")
val original = hir_function("resolved", Some(verification_contract()))
var resolver = MethodResolver.new(SymbolTable.new())
val resolved = resolver.resolve_function(original)
expect(resolved.verification_contract.?).to_equal(true)
val retained = resolved.verification_contract ?? verification_contract()
expect(retained.clauses.len()).to_equal(1)
expect(retained.proof_uses).to_equal("ContractProof.valid")
expect(retained.outcome == HirContractOutcome.Plain).to_equal(true)
```

</details>

#### retains the resolved contract on the lowered MIR function

- retains the resolved contract on the lowered MIR function
- Lower the resolved HIR function through the public MIR boundary
   - Expected: mir_function.verification_contract.? is true
   - Expected: retained.clauses.len() equals `1`
   - Expected: retained.proof_uses equals `ContractProof.valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains the resolved contract on the lowered MIR function")
step("Lower the resolved HIR function through the public MIR boundary")
val original = hir_function("lowered", Some(verification_contract()))
var resolver = MethodResolver.new(SymbolTable.new())
val resolved = resolver.resolve_function(original)
var lowering = MirLowering.new(SymbolTable.new())
val mir_function = lowering.lower_function(resolved)
expect(mir_function.verification_contract.?).to_equal(true)
val retained = mir_function.verification_contract ?? verification_contract()
expect(retained.clauses.len()).to_equal(1)
expect(retained.proof_uses).to_equal("ContractProof.valid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR verification contract preservation.
- HIR verification contract preservation

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4958e1269c738d4d1af0229c2f2d4f25950532f321b6429784be926077d7cf2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4958e1269c738d4d1af0229c2f2d4f25950532f321b6429784be926077d7cf2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4958e1269c738d4d1af0229c2f2d4f25950532f321b6429784be926077d7cf2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_verification_contract_preservation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_verification_contract_preservation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_verification_contract_preservation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the ordinary constructor path explicitly contract-free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a non-nil contract through semantic resolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the resolved contract on the lowered MIR function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
