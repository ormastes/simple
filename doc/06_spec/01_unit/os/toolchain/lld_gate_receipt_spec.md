# P6 lld Toolchain Gate — Fail-Closed Evidence Receipt

> Verifies the lld gate receipt behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P6 lld Toolchain Gate — Fail-Closed Evidence Receipt

Verifies the lld gate receipt behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented (encodes a BLOCKED gate honestly) |
| Requirements | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (P6) |
| Source | `test/01_unit/os/toolchain/lld_gate_receipt_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the lld gate receipt behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### P6 lld gate evidence receipts

#### the authored gate script yields a PASS receipt

- Verify: the authored gate script yields a PASS receipt
- Observe the gate script on disk via app.io facades
- Verify a receipt claiming the script as its artifact
   - Expected: verify_verdict(outcome) equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-P6
step("Verify: the authored gate script yields a PASS receipt")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe the gate script on disk via app.io facades")
val script_exists = file_exists(GATE_SCRIPT)
val script_mtime = file_modified_time(GATE_SCRIPT)
step("Verify a receipt claiming the script as its artifact")
val receipt = receipt_new("p6_lld_gate_script_authored", "generic", "hosted", "PASS", GATE_SCRIPT)
val outcome = receipt_verify(receipt, script_exists, script_mtime, 0)
if not outcome.passed:
    print("gate-script receipt failed rule " + outcome.rule + ": " + outcome.reason)
expect(verify_verdict(outcome)).to_equal("PASS")
```

</details>

#### the blocked lld_static artifact fails closed — the honest current state

- Verify: the blocked lld_static artifact fails closed — the honest current state
- Observe that the lld_static build product does not exist
- A receipt for the missing gate product must verify FAIL
   - Expected: verify_verdict(outcome) equals `FAIL`
   - Expected: outcome.rule equals `artifact_present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-P6
step("Verify: the blocked lld_static artifact fails closed — the honest current state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe that the lld_static build product does not exist")
val bin_exists = file_exists(LLD_STATIC_BIN)
step("A receipt for the missing gate product must verify FAIL")
val receipt = receipt_new("p6_lld_gate_link_run", "generic", "blocked", "BLOCKED", LLD_STATIC_BIN)
val outcome = receipt_verify(receipt, bin_exists, 0, 0)
expect(verify_verdict(outcome)).to_equal("FAIL")
expect(outcome.rule).to_equal("artifact_present")
expect(outcome.reason).to_contain("missing_artifact")
```

</details>

#### the blocked receipt serializes its blocked state into SDN

- Verify: the blocked receipt serializes its blocked state into SDN
- Serialize the blocked-run receipt for the ledger


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-P6
step("Verify: the blocked receipt serializes its blocked state into SDN")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Serialize the blocked-run receipt for the ledger")
val receipt = receipt_new("p6_lld_gate_link_run", "generic", "blocked", "BLOCKED", LLD_STATIC_BIN)
val sdn = receipt_to_sdn(receipt)
expect(sdn).to_contain("evidence_receipt:")
expect(sdn).to_contain("machine_or_qemu: blocked")
expect(sdn).to_contain("result: BLOCKED")
expect(sdn).to_contain("artifacts: " + LLD_STATIC_BIN)
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


## Related Documentation

- **Requirements:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (P6)`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6477c46a224dcefc050761850788750305771ef47aab6a76915e95d4f7418b85`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6477c46a224dcefc050761850788750305771ef47aab6a76915e95d4f7418b85`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6477c46a224dcefc050761850788750305771ef47aab6a76915e95d4f7418b85`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/toolchain/lld_gate_receipt_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
