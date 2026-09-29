# Verification Obligation Module Specification

> Tests covering Verification 2.0 canonical module obligation closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verification Obligation Module Specification

## Scenarios

### Verification 2.0 canonical module obligation closure

#### binds an exact pure leaf callee contract into the owner call VC

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds an exact pure leaf callee contract into the owner call VC
   - Expected: closure.closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds an exact pure leaf callee contract into the owner call VC")
val callee = module_function(7101, "leaf", [])
val owner = module_function(7102, "owner", [module_call("leaf")])
val closure = generate_verification_obligation_closure_from_canonical_module_v1(
    module_with(owner, callee), "7102", "woven-module", "lean4",
    "lean-backend-v1", closed_module_trust())
expect(closure.closed()).to_equal(true)
expect(closure.root_obligation_id).to_equal(
    "7102::fv2::trust-closure")
```

</details>

#### requires a resolver-backed exact call manifest for the V2 handoff

- requires a resolver-backed exact call manifest for the V2 handoff
   - Expected: resolved.closed() is true
   - Expected: resolved.resolved_call_manifest_hash == "" is false
   - Expected: resolved.hash() == resolved.closure.closure_hash is false
   - Expected: substituted.closed() is true
   - Expected: substituted.hash() == resolved.hash() is false
   - Expected: rejected.closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a resolver-backed exact call manifest for the V2 handoff")
val callee = module_function(7101, "leaf", [])
val owner = module_function(7102, "owner", [module_call("leaf")])
val module = module_with(owner, callee)
val resolved = generate_resolved_verification_obligation_closure_from_canonical_module_v2(
    module, "7102", "woven-module", "lean4", "lean-backend-v1",
    closed_module_trust(), resolved_module_calls(module, owner, callee))
expect(resolved.closed()).to_equal(true)
expect(resolved.resolved_call_manifest_hash == "").to_equal(false)
expect(resolved.hash() == resolved.closure.closure_hash).to_equal(false)
var substituted_manifest = resolved_module_calls(module, owner, callee)
substituted_manifest.resolver_receipt_hash = sha256_text("other-resolver-receipt")
val substituted = generate_resolved_verification_obligation_closure_from_canonical_module_v2(
    module, "7102", "woven-module", "lean4", "lean-backend-v1",
    closed_module_trust(), substituted_manifest)
expect(substituted.closed()).to_equal(true)
expect(substituted.hash() == resolved.hash()).to_equal(false)
val missing = ResolvedDirectCallManifestV1(
    resolved_direct_call_module_hash_v1(module), sha256_text("resolver-receipt"), [])
val rejected = generate_resolved_verification_obligation_closure_from_canonical_module_v2(
    module, "7102", "woven-module", "lean4", "lean-backend-v1",
    closed_module_trust(), missing)
expect(rejected.closed()).to_equal(false)
expect(rejected.diagnostic).to_contain("CALL-IDENTITY-MISSING")
```

</details>

#### invalidates the closure when the callee contract changes

- invalidates the closure when the callee contract changes
   - Expected: first.closure_hash == second.closure_hash is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates the closure when the callee contract changes")
val callee = module_function(7101, "leaf", [])
val owner = module_function(7102, "owner", [module_call("leaf")])
val first = generate_verification_obligation_closure_from_canonical_module_v1(
    module_with(owner, callee), "7102", "woven-module", "lean4",
    "lean-backend-v1", closed_module_trust())
var changed = callee
val span = module_span()
val bool_type = HirType(kind: HirTypeKind.Bool, span: span)
val predicate = HirExpr(kind: HirExprKind.BoolLit(false), has_type_: true,
    type_: bool_type, span: span)
changed.verification_contract = Some(HirContractBlock(clauses: [
    HirContractClause(kind: HirContractClauseKind.Requires,
        predicate: predicate, binding_name: "", span: span)],
    proof_uses: "ModuleProof.correct", outcome: HirContractOutcome.Plain))
val second = generate_verification_obligation_closure_from_canonical_module_v1(
    module_with(owner, changed), "7102", "woven-module", "lean4",
    "lean-backend-v1", closed_module_trust())
expect(first.closure_hash == second.closure_hash).to_equal(false)
```

</details>

#### rejects missing contracts and effectful leaf calls

- rejects missing contracts and effectful leaf calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing contracts and effectful leaf calls")
val owner = module_function(7102, "owner", [module_call("leaf")])
val unchecked = module_function(7101, "leaf", [], false)
val missing = generate_verification_obligation_closure_from_canonical_module_v1(
    module_with(owner, unchecked), "7102", "woven-module", "lean4",
    "lean-backend-v1", closed_module_trust())
expect(missing.diagnostic).to_contain("CALL-CONTRACT")
val value = MirOperand(kind: MirOperandKind.Const(
    MirConstValue.Int(1), MirType.i64()))
val effectful = module_function(7101, "leaf", [MirInst(
    kind: MirInstKind.StoreGlobal(SymbolId(id: 99), value),
    span: Some(module_span()))])
val rejected = generate_verification_obligation_closure_from_canonical_module_v1(
    module_with(owner, effectful), "7102", "woven-module", "lean4",
    "lean-backend-v1", closed_module_trust())
expect(rejected.diagnostic).to_contain("CALL-EFFECT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/verification_obligation_module_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Verification 2.0 canonical module obligation closure.
- Verification 2.0 canonical module obligation closure

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b76c791c96f6678eb90abd8a6cdfea737d9134f7d459a2672bf03fb5fd15cfbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b76c791c96f6678eb90abd8a6cdfea737d9134f7d459a2672bf03fb5fd15cfbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b76c791c96f6678eb90abd8a6cdfea737d9134f7d459a2672bf03fb5fd15cfbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/verification_obligation_module_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/verification_obligation_module_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/verification_obligation_module_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/verification_obligation_module_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/verification_obligation_module_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds an exact pure leaf callee contract into the owner call VC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/verification_obligation_module_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a resolver-backed exact call manifest for the V2 handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/verification_obligation_module_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates the closure when the callee contract changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
