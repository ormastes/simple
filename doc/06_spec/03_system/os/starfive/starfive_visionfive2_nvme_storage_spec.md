# StarFive VisionFive 2 NVMe safety contract

> Keep read-only identification separate from explicitly authorized provisioning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# StarFive VisionFive 2 NVMe safety contract

Keep read-only identification separate from explicitly authorized provisioning.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keep read-only identification separate from explicitly authorized provisioning.
Incomplete live paths must report BLOCKED and must never claim physical PASS.

## Scenarios

#### BLOCKED: StarFive live NVMe evidence unavailable ({phase}) _(pending)_
### StarFive VisionFive 2 NVMe storage safety

#### publishes distinct identify and provision contracts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes distinct identify and provision contracts
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes distinct identify and provision contracts")
val (out, err, code) = run_nvme_check("--contract")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("starfive_nvme_contract_status=pass")
expect(out).to_contain("identify_mode=read-only")
expect(out).to_contain("identify_writes=0")
expect(out).to_contain("provision_mode=separately-authorized")
```

</details>

#### checks the fail-closed storage policy

- checks the fail-closed storage policy
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks the fail-closed storage policy")
val (out, err, code) = run_nvme_check("--self-test")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("starfive_nvme_self_test_status=pass")
expect(out).to_contain("changed_identity=blocked")
expect(out).to_contain("mounted_device=blocked")
expect(out).to_contain("boot_source_device=blocked")
```

</details>

#### checks live identify is implemented and requires physical proof

- checks live identify is implemented and requires physical proof
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks live identify is implemented and requires physical proof")
val (out, err, code) = run_nvme_check("--identify-live")
expect(err).to_equal("")
require_nvme_pass(out, code, "identify-live")
```

</details>

#### blocks provisioning without a live immutable identity receipt

- blocks provisioning without a live immutable identity receipt
   - Expected: code equals `2`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks provisioning without a live immutable identity receipt")
val (out, err, code) = run_nvme_check("--provision-live")
expect(code).to_equal(2)
expect(err).to_equal("")
expect(out).to_contain("starfive_nvme_status=blocked")
expect(out).to_contain("starfive_nvme_reason=identify-receipt-missing")
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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `44e66286e1e0153f9a707de7a97f429827baa9e47514eec99b1b8b8eb32163f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44e66286e1e0153f9a707de7a97f429827baa9e47514eec99b1b8b8eb32163f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44e66286e1e0153f9a707de7a97f429827baa9e47514eec99b1b8b8eb32163f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl
mirror: doc/06_spec/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 9 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes distinct identify and provision contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks the fail-closed storage policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks live identify is implemented and requires physical proof' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
