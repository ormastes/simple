# Verification Call Identity Specification

> Tests covering Verification 2.0 resolved direct-call identity adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verification Call Identity Specification

## Scenarios

### Verification 2.0 resolved direct-call identity adapter

#### finalizes resolver captures only against the exact completed MIR snapshot

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finalizes resolver captures only against the exact completed MIR snapshot
   - Expected: manifest.bindings[0].callee_symbol_id equals `9201`
   - Expected: missing.is_err() is true
   - Expected: duplicate.is_err() is true
   - Expected: boundary.is_err() is true
   - Expected: site.is_err() is true
   - Expected: invalid_receipt.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finalizes resolver captures only against the exact completed MIR snapshot")
val callee = identity_function(9201, "leaf", [])
val owner = identity_function(9202, "owner", [identity_call("leaf")])
val module = identity_module(owner, callee)
val capture = ResolvedDirectCallCaptureV1("9202", 0, 0, "9201")
match finalize_resolved_direct_call_manifest_v1(module,
        sha256_text("resolver-receipt"), [capture]):
    case Ok(manifest):
        expect(validate_resolved_direct_call_manifest_v1(module,
            manifest).closed()).to_equal(true)
        expect(manifest.bindings[0].callee_symbol_id).to_equal("9201")
    case Err(message): expect(message).to_equal("")

val missing = finalize_resolved_direct_call_manifest_v1(module,
    sha256_text("resolver-receipt"), [])
expect(missing.is_err()).to_equal(true)
match missing:
    case Err(message): expect(message).to_contain("CALL-IDENTITY-MISSING")
    case Ok(_): expect("finalized").to_equal("missing")

val duplicate = finalize_resolved_direct_call_manifest_v1(module,
    sha256_text("resolver-receipt"), [capture, capture])
expect(duplicate.is_err()).to_equal(true)
match duplicate:
    case Err(message): expect(message).to_contain("FINALIZER-DUPLICATE")
    case Ok(_): expect("finalized").to_equal("duplicate")

val external = ResolvedDirectCallCaptureV1("9202", 0, 0, "9999")
val boundary = finalize_resolved_direct_call_manifest_v1(module,
    sha256_text("resolver-receipt"), [external])
expect(boundary.is_err()).to_equal(true)
match boundary:
    case Err(message): expect(message).to_contain("FINALIZER-BOUNDARY")
    case Ok(_): expect("finalized").to_equal("boundary")

val absent_site = ResolvedDirectCallCaptureV1("9202", 0, 1, "9201")
val site = finalize_resolved_direct_call_manifest_v1(module,
    sha256_text("resolver-receipt"), [absent_site])
expect(site.is_err()).to_equal(true)
match site:
    case Err(message): expect(message).to_contain("FINALIZER-SITE")
    case Ok(_): expect("finalized").to_equal("site")

val invalid_receipt = finalize_resolved_direct_call_manifest_v1(module,
    "not-a-hash", [capture])
expect(invalid_receipt.is_err()).to_equal(true)
match invalid_receipt:
    case Err(message): expect(message).to_contain("FINALIZER-RECEIPT")
    case Ok(_): expect("finalized").to_equal("receipt")
```

</details>

#### binds an unchanged direct call to its exact SymbolId and callee snapshot

- binds an unchanged direct call to its exact SymbolId and callee snapshot
   - Expected: closure.closed() is true
   - Expected: closure.call_site_hashes.len() equals `1`
   - Expected: effects.diagnostic equals ``
   - Expected: effects.nodes[1].symbol_id equals `9202`
   - Expected: effects.nodes[1].transitive_effects.len() equals `0`
   - Expected: vir.closure_ready() is true
   - Expected: vir.vir.functions[1].called_symbols[0].id equals `9201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds an unchanged direct call to its exact SymbolId and callee snapshot")
val callee = identity_function(9201, "leaf", [])
val owner = identity_function(9202, "owner", [identity_call("leaf")])
val module = identity_module(owner, callee)
val closure = validate_resolved_direct_call_manifest_v1(module,
    identity_manifest(module, owner, callee))
expect(closure.closed()).to_equal(true)
expect(closure.call_site_hashes.len()).to_equal(1)
match resolved_direct_call_callee_symbol_v1(module,
        identity_manifest(module, owner, callee), owner, 0, 0):
    case Ok(symbol): expect(symbol).to_equal("9201")
    case Err(message): expect(message).to_equal("")
val effects = verification_effect_closure_from_resolved_mir_module_v2(
    module, identity_manifest(module, owner, callee))
expect(effects.diagnostic).to_equal("")
expect(effects.nodes[1].symbol_id).to_equal("9202")
expect(effects.nodes[1].transitive_effects.len()).to_equal(0)
val vir = verification_ir_module_from_resolved_mir_v2(module,
    sha256_text("source"), sha256_text("expanded"),
    sha256_text("woven"), sha256_text("policy"),
    identity_manifest(module, owner, callee))
expect(vir.closure_ready()).to_equal(true)
expect(vir.vir.functions[1].called_symbols[0].id).to_equal(9201)
```

</details>

#### rejects stale callee bodies and mismatched textual targets

- rejects stale callee bodies and mismatched textual targets
   - Expected: missing_effects.diagnostic == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects stale callee bodies and mismatched textual targets")
val callee = identity_function(9201, "leaf", [])
val owner = identity_function(9202, "owner", [identity_call("leaf")])
val module = identity_module(owner, callee)
var stale = identity_manifest(module, owner, callee)
stale.bindings[0].callee_body_hash = sha256_text("forged-body")
expect(validate_resolved_direct_call_manifest_v1(module, stale).diagnostic)
    .to_contain("STALE")
val renamed = identity_function(9201, "other", [])
val renamed_module = identity_module(owner, renamed)
val mismatch = identity_manifest(renamed_module, owner, renamed)
expect(validate_resolved_direct_call_manifest_v1(renamed_module, mismatch).diagnostic)
    .to_contain("NAME")
val missing_effects = verification_effect_closure_from_resolved_mir_module_v2(
    module, ResolvedDirectCallManifestV1(
        resolved_direct_call_module_hash_v1(module),
        sha256_text("resolver-receipt"), []))
expect(missing_effects.diagnostic == "").to_equal(false)
expect(missing_effects.diagnostic).to_contain("CALL-IDENTITY-MISSING")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/verification_call_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Verification 2.0 resolved direct-call identity adapter.
- Verification 2.0 resolved direct-call identity adapter

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

- Canonical SPipe generation for source `34bbab9b35183ec800ad674ccc0ad9d515d655bf02274d1ffd1fc98becbf8207`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `34bbab9b35183ec800ad674ccc0ad9d515d655bf02274d1ffd1fc98becbf8207`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `34bbab9b35183ec800ad674ccc0ad9d515d655bf02274d1ffd1fc98becbf8207`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/verification_call_identity_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/verification_call_identity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/verification_call_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/verification_call_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/verification_call_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/verification_call_identity_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finalizes resolver captures only against the exact completed MIR snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/verification_call_identity_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds an unchanged direct call to its exact SymbolId and callee snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/verification_call_identity_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale callee bodies and mismatched textual targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
