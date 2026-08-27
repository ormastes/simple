# X86 64 Fs Loaded Launch Proof Specification

> Tests covering x86_64 fs-loaded launch proof.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Fs Loaded Launch Proof Specification

## Scenarios

### x86_64 fs-loaded launch proof

#### accepts direct filesystem process-backed tool app proof

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts direct filesystem process-backed tool app proof
   - Expected: proofs.len() equals `6`
   - Expected: all_tool_apps_have_base_proof(serial) is true
   - Expected: tool_apps_serial_accepts_completion(serial) is true
   - Expected: has_resident_manifest_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts direct filesystem process-backed tool app proof")
val serial = process_backed_tool_app_serial()
val proofs = classify_all_tool_app_proofs(serial)

expect(proofs.len()).to_equal(6)
expect(all_tool_apps_have_base_proof(serial)).to_equal(true)
expect(tool_apps_serial_accepts_completion(serial)).to_equal(true)
expect(has_resident_manifest_fallback(serial)).to_equal(false)
```

</details>

#### rejects resident-manifest fallback as completion evidence

- rejects resident-manifest fallback as completion evidence
   - Expected: proofs.len() equals `6`
   - Expected: has_resident_manifest_fallback(serial) is true
   - Expected: all_tool_apps_have_base_proof(serial) is false
   - Expected: tool_apps_serial_accepts_completion(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects resident-manifest fallback as completion evidence")
val serial = resident_manifest_fallback_serial()
val proofs = classify_all_tool_app_proofs(serial)

expect(proofs.len()).to_equal(6)
expect(has_resident_manifest_fallback(serial)).to_equal(true)
expect(all_tool_apps_have_base_proof(serial)).to_equal(false)
expect(tool_apps_serial_accepts_completion(serial)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/x86_64_fs_loaded_launch_proof_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_64 fs-loaded launch proof.
- x86_64 fs-loaded launch proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `dad0e650b427e3fec46d0b568f46632dc2fc3ef6b4eba0586c152baa225bbd45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dad0e650b427e3fec46d0b568f46632dc2fc3ef6b4eba0586c152baa225bbd45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dad0e650b427e3fec46d0b568f46632dc2fc3ef6b4eba0586c152baa225bbd45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/x86_64_fs_loaded_launch_proof_spec.spl
mirror: doc/06_spec/unit/os/x86_64_fs_loaded_launch_proof_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/x86_64_fs_loaded_launch_proof_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/x86_64_fs_loaded_launch_proof_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/x86_64_fs_loaded_launch_proof_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/x86_64_fs_loaded_launch_proof_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts direct filesystem process-backed tool app proof' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/x86_64_fs_loaded_launch_proof_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects resident-manifest fallback as completion evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
