# P6 lld Toolchain Gate — Fail-Closed Evidence Receipt

> The in-guest lld link gate (`scripts/os/ssh_lld_link_uefi.shs`) is authored but not yet runnable: no `lld_static` build product exists on this host, so the gate has an honest blocked row in the production status ledger. This spec turns that prose row into machine-checked fail-closed evidence using `std.spec.evidence_receipt` (§21.4):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P6 lld Toolchain Gate — Fail-Closed Evidence Receipt

The in-guest lld link gate (`scripts/os/ssh_lld_link_uefi.shs`) is authored but not yet runnable: no `lld_static` build product exists on this host, so the gate has an honest blocked row in the production status ledger. This spec turns that prose row into machine-checked fail-closed evidence using `std.spec.evidence_receipt` (§21.4):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented (encodes a BLOCKED gate honestly) |
| Requirements | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (P6) |
| Source | `test/01_unit/os/toolchain/lld_gate_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The in-guest lld link gate (`scripts/os/ssh_lld_link_uefi.shs`) is authored
but not yet runnable: no `lld_static` build product exists on this host, so
the gate has an honest blocked row in the production status ledger. This
spec turns that prose row into machine-checked fail-closed evidence using
`std.spec.evidence_receipt` (§21.4):

- a receipt whose artifact is the gate SCRIPT verifies PASS (the gate is
  authored and present on disk), and
- a receipt whose artifact is the `lld_static` binary the gate needs
  verifies FAIL via the missing-artifact rule — FAIL **is** the current
  truth, and this spec passes by asserting exactly that verdict.

When someone lands `lld_static` and runs the gate, the second example goes
red, forcing the receipt (and the ledger row) to be upgraded to a real run
receipt instead of silently rotting.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Gate script | `scripts/os/ssh_lld_link_uefi.shs` (authored, not yet run) |
| Blocked artifact | `build/os/clang_static/bin/lld_static` (does not exist) |
| Fail-closed rule | missing artifact -> FAIL, never a silent pass |

## Scenarios

### P6 lld gate evidence receipts

#### the authored gate script yields a PASS receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the authored gate script yields a PASS receipt
- Observe the gate script on disk via app.io facades
- Verify a receipt claiming the script as its artifact
   - Expected: verify_verdict(outcome) equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the authored gate script yields a PASS receipt")
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

- the blocked lld_static artifact fails closed — the honest current state
- Observe that the lld_static build product does not exist
- A receipt for the missing gate product must verify FAIL
   - Expected: verify_verdict(outcome) equals `FAIL`
   - Expected: outcome.rule equals `artifact_present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the blocked lld_static artifact fails closed — the honest current state")
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

- the blocked receipt serializes its blocked state into SDN
- Serialize the blocked-run receipt for the ledger


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the blocked receipt serializes its blocked state into SDN")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SIMPLEOS-HARDEN-P6`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `44e928bd71ec44d1512fea9162cdc381ce85750c1148ca8cb3a625774eaf22ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44e928bd71ec44d1512fea9162cdc381ce85750c1148ca8cb3a625774eaf22ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44e928bd71ec44d1512fea9162cdc381ce85750c1148ca8cb3a625774eaf22ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/toolchain/lld_gate_receipt_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain/lld_gate_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/toolchain/lld_gate_receipt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/toolchain/lld_gate_receipt_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the authored gate script yields a PASS receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain/lld_gate_receipt_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the blocked lld_static artifact fails closed — the honest current state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain/lld_gate_receipt_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the blocked receipt serializes its blocked state into SDN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
