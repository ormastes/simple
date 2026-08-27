# Simple Erp Catalog Specification

> Tests covering simple erp catalog.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Erp Catalog Specification

## Scenarios

### simple erp catalog

#### defines easy and pro mode business lanes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines easy and pro mode business lanes
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines easy and pro mode business lanes")
val result = shell("bin/release/x86_64-unknown-linux-gnu/simple examples/12_business/simple_erp/src/catalog.spl")
expect(result.exit_code).to_equal(0)
val summary = result.stdout
expect summary.contains("easy mode")
expect summary.contains("pro mode")
expect summary.contains("crm")
expect summary.contains("reservation")
expect summary.contains("selling")
```

</details>

#### defines implemented workflow evidence

- defines implemented workflow evidence
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines implemented workflow evidence")
val result = shell("bin/release/x86_64-unknown-linux-gnu/simple examples/12_business/simple_erp/src/catalog.spl")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("open leads")
expect(result.stdout).to_contain("open slots")
expect(result.stdout).to_contain("unpaid")
expect(result.stdout).to_contain("pipeline=540000")
expect(result.stdout).to_contain("approved_quotes=250000")
expect(result.stdout).to_contain("reservation_open_slots=7")
expect(result.stdout).to_contain("unpaid_sales=49500")
expect(result.stdout).to_contain("selling_channels=5")
expect(result.stdout).to_contain("payment_audits=5")
expect(result.stdout).to_contain("inventory_available=141")
expect(result.stdout).to_contain("fulfillable_orders=2")
expect(result.stdout).to_contain("rbac=3 roles")
expect(result.stdout).to_contain("audit=enabled")
expect(result.stdout).to_contain("fulfillment=paid-stock")
expect(result.stdout).to_contain("tenant=tenant-simple-demo")
expect(result.stdout).to_contain("active_sessions=1")
expect(result.stdout).to_contain("ledger_entries=3")
expect(result.stdout).to_contain("ledger_total=13500")
expect(result.stdout).to_contain("idempotency=pass")
expect(result.stdout).to_contain("recovery=3 checks")
expect(result.stdout).to_contain("audit_chain=valid")
expect(result.stdout).to_contain("redaction=pass")
expect(result.stdout).to_contain("health=3 ok")
expect(result.stdout).to_contain("restore_parity=pass")
expect(result.stdout).to_contain("schema=3")
expect(result.stdout).to_contain("migrations=3 applied")
expect(result.stdout).to_contain("snapshot=consistent")
expect(result.stdout).to_contain("restore_snapshot=pass")
expect(result.stdout).to_contain("durable_snapshot=missing")
expect(result.stdout).to_contain("Production durability")
expect(result.stdout).to_contain("status=blocked-durable-store")
expect(result.stdout).to_contain("guarded_writes=3 allowed")
expect(result.stdout).to_contain("denied=2")
expect(result.stdout).to_contain("receipts=3")
expect(result.stdout).to_contain("gates=session+rbac+validation+audit+ledger")
expect(result.stdout).to_contain("gates=7/8")
expect(result.stdout).to_contain("status=blocked-durable-store")
```

</details>

#### selects easy and pro interfaces

- selects easy and pro interfaces
   - Expected: easy.exit_code equals `0`
   - Expected: pro.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects easy and pro interfaces")
val easy = shell("bin/release/x86_64-unknown-linux-gnu/simple examples/12_business/simple_erp/src/catalog.spl easy")
expect(easy.exit_code).to_equal(0)
expect(easy.stdout).to_start_with("Easy ERP")
expect(easy.stdout).to_contain("open leads")
val pro = shell("bin/release/x86_64-unknown-linux-gnu/simple examples/12_business/simple_erp/src/catalog.spl pro")
expect(pro.exit_code).to_equal(0)
expect(pro.stdout).to_start_with("Pro ERP")
expect(pro.stdout).to_contain("payment_audits=5")
expect(pro.stdout).to_contain("inventory_available=141")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple erp catalog.
- simple erp catalog

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33b8996afac9b6b0d8df2152908dfd1b75810107b41628b17cbafba9d5a59c62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33b8996afac9b6b0d8df2152908dfd1b75810107b41628b17cbafba9d5a59c62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33b8996afac9b6b0d8df2152908dfd1b75810107b41628b17cbafba9d5a59c62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl
mirror: doc/06_spec/03_system/app/simple_erp/feature/simple_erp_catalog_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_erp/feature/simple_erp_catalog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_erp/feature/simple_erp_catalog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines easy and pro mode business lanes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines implemented workflow evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects easy and pro interfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
