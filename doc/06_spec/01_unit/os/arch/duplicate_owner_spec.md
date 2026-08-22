# SimpleOS Duplicate-Owner Architecture Guard

> Verifies the duplicate owner behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Duplicate-Owner Architecture Guard

Verifies the duplicate owner behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Requirements | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (Stage S) |
| Source | `test/01_unit/os/arch/duplicate_owner_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the duplicate owner behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS duplicate-owner architecture guard

#### freezes the kernel contract at ABI v1

- Verify: freezes the kernel contract at ABI v1
- Read the ABI version from the frozen contract index
   - Expected: abi_v1_major() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: freezes the kernel contract at ABI v1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Read the ABI version from the frozen contract index")
expect(abi_v1_major()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### every frozen canonical owner exists on disk

- Verify: every frozen canonical owner exists on disk
- Map each canonical owner module to its source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: every frozen canonical owner exists on disk")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Map each canonical owner module to its source file")
val owners = abi_v1_canonical_owners()
expect(owners.len()).to_be_greater_than(10)
for owner in owners:
    val path = owner_source_path(owner)
    if not file_exists(path):
        print("missing canonical owner source: " + path)
    expect(file_exists(path)).to_be(true)
```

</details>

#### the production status ledger names the core subsystem owners

- Verify: the production status ledger names the core subsystem owners
- Read the production status ledger
- Check ledger covers the enforced subsystems


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: the production status ledger names the core subsystem owners")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Read the production status ledger")
expect(file_exists(LEDGER_PATH)).to_be(true)
val ledger = file_read_text(LEDGER_PATH)
expect(ledger).to_contain("production_status:")
step("Check ledger covers the enforced subsystems")
expect(ledger).to_contain("os.kernel.abi.abi_v1")
expect(ledger).to_contain("os.kernel.types")
expect(ledger).to_contain("os.kernel.ipc")
expect(ledger).to_contain("os.kernel.loader")
expect(ledger).to_contain("os.kernel.fs")
expect(ledger).to_contain("cspace_spawn")
expect(ledger).to_contain("maturity:")
```

</details>

#### no parallel duplicate trees shadow frozen subsystems

- Verify: no parallel duplicate trees shadow frozen subsystems
- Scan OS sources for banned duplicate-suffix names


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: no parallel duplicate trees shadow frozen subsystems")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Scan OS sources for banned duplicate-suffix names")
Then_no_duplicate_trees("find src/os -name '*_v2.spl' -not -path '*vendor*'")
Then_no_duplicate_trees("find src/os -name 'new_vfs*' -o -name 'fast_loader2*'")
```

</details>

### Duplicate-owner guard fail-closed calibration

#### the scan helper detects a known-present file

- Verify: the scan helper detects a known-present file
   - Expected: hits equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: the scan helper detects a known-present file")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val lines = shell_lines("find test/01_unit/os/arch -name 'duplicate_owner_spec.spl'")
var hits = 0
for line in lines:
    if line != "":
        hits = hits + 1
expect(hits).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

### Ledger parity emits a fail-closed evidence receipt

#### the production status ledger receipt verdict is PASS

- Verify: the production status ledger receipt verdict is PASS
- Observe ledger existence and mtime via app.io facades
- Build a receipt claiming the ledger as its artifact and verify fail-closed
   - Expected: verify_verdict(outcome) equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: the production status ledger receipt verdict is PASS")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe ledger existence and mtime via app.io facades")
val ledger_exists = file_exists(LEDGER_PATH)
val ledger_mtime = file_modified_time(LEDGER_PATH)
step("Build a receipt claiming the ledger as its artifact and verify fail-closed")
val receipt = receipt_new("duplicate_owner_ledger_parity", "generic", "hosted", "PASS", LEDGER_PATH)
val outcome = receipt_verify(receipt, ledger_exists, ledger_mtime, 0)
if not outcome.passed:
    print("ledger receipt failed rule " + outcome.rule + ": " + outcome.reason)
expect(verify_verdict(outcome)).to_equal("PASS")
```

</details>

#### a receipt for a nonexistent artifact fails closed

- Verify: a receipt for a nonexistent artifact fails closed
- Build a receipt whose declared artifact does not exist on disk
- Missing artifact must yield FAIL, never a silent pass
   - Expected: verify_verdict(outcome) equals `FAIL`
   - Expected: outcome.rule equals `artifact_present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-S3
step("Verify: a receipt for a nonexistent artifact fails closed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build a receipt whose declared artifact does not exist on disk")
val ghost = "doc/08_tracking/os/__no_such_ledger__.sdn"
val receipt = receipt_new("duplicate_owner_ledger_parity_red", "generic", "hosted", "PASS", ghost)
val outcome = receipt_verify(receipt, file_exists(ghost), 0, 0)
step("Missing artifact must yield FAIL, never a silent pass")
expect(verify_verdict(outcome)).to_equal("FAIL")
expect(outcome.rule).to_equal("artifact_present")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (Stage S)`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `180e89f6de96f597fe03d484b3deac8b04387f6d9f2a419eeba55cfe26d2e9c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `180e89f6de96f597fe03d484b3deac8b04387f6d9f2a419eeba55cfe26d2e9c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `180e89f6de96f597fe03d484b3deac8b04387f6d9f2a419eeba55cfe26d2e9c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/arch/duplicate_owner_spec.spl
mirror: doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
