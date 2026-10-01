# SimpleOS Duplicate-Owner Architecture Guard

> Enforces master-plan §4/§24: one canonical owner per kernel subsystem. Fails closed when the frozen ABI v1 owner list drifts from disk or from the production status ledger, and when a parallel duplicate tree (`*_v2.spl`, `new_vfs*`, `fast_loader2*`) appears under the OS sources.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Duplicate-Owner Architecture Guard

Enforces master-plan §4/§24: one canonical owner per kernel subsystem. Fails closed when the frozen ABI v1 owner list drifts from disk or from the production status ledger, and when a parallel duplicate tree (`*_v2.spl`, `new_vfs*`, `fast_loader2*`) appears under the OS sources.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Requirements | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (Stage S) |
| Source | `test/01_unit/os/arch/duplicate_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Enforces master-plan §4/§24: one canonical owner per kernel subsystem. Fails
closed when the frozen ABI v1 owner list drifts from disk or from the
production status ledger, and when a parallel duplicate tree (`*_v2.spl`,
`new_vfs*`, `fast_loader2*`) appears under the OS sources.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ABI v1 index | `os.kernel.abi.abi_v1` freezes owners by reference |
| Ledger | `doc/08_tracking/os/production_status.sdn` maturity + owner per subsystem |

## Scenarios

### SimpleOS duplicate-owner architecture guard

#### freezes the kernel contract at ABI v1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- freezes the kernel contract at ABI v1
- Read the ABI version from the frozen contract index
   - Expected: abi_v1_major() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("freezes the kernel contract at ABI v1")
step("Read the ABI version from the frozen contract index")
expect(abi_v1_major()).to_equal(1)
```

</details>

#### every frozen canonical owner exists on disk

- every frozen canonical owner exists on disk
- Map each canonical owner module to its source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("every frozen canonical owner exists on disk")
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

- the production status ledger names the core subsystem owners
- Read the production status ledger
- Check ledger covers the enforced subsystems


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the production status ledger names the core subsystem owners")
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

- no parallel duplicate trees shadow frozen subsystems
- Scan OS sources for banned duplicate-suffix names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("no parallel duplicate trees shadow frozen subsystems")
step("Scan OS sources for banned duplicate-suffix names")
Then_no_duplicate_trees("find src/os -name '*_v2.spl' -not -path '*vendor*'")
Then_no_duplicate_trees("find src/os -name 'new_vfs*' -o -name 'fast_loader2*'")
```

</details>

### Duplicate-owner guard fail-closed calibration

#### the scan helper detects a known-present file

- the scan helper detects a known-present file
   - Expected: hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the scan helper detects a known-present file")
val lines = shell_lines("find test/01_unit/os/arch -name 'duplicate_owner_spec.spl'")
var hits = 0
for line in lines:
    if line != "":
        hits = hits + 1
expect(hits).to_equal(1)
```

</details>

### Ledger parity emits a fail-closed evidence receipt

#### the production status ledger receipt verdict is PASS

- the production status ledger receipt verdict is PASS
- Observe ledger existence and mtime via app.io facades
- Build a receipt claiming the ledger as its artifact and verify fail-closed
   - Expected: verify_verdict(outcome) equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the production status ledger receipt verdict is PASS")
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

- a receipt for a nonexistent artifact fails closed
- Build a receipt whose declared artifact does not exist on disk
- Missing artifact must yield FAIL, never a silent pass
   - Expected: verify_verdict(outcome) equals `FAIL`
   - Expected: outcome.rule equals `artifact_present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a receipt for a nonexistent artifact fails closed")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SIMPLEOS-HARDEN-S3`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91c82b432df0a0e73e9f704b2ef5d8eee624527d70c5cc47316227f10a85e1e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91c82b432df0a0e73e9f704b2ef5d8eee624527d70c5cc47316227f10a85e1e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91c82b432df0a0e73e9f704b2ef5d8eee624527d70c5cc47316227f10a85e1e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/arch/duplicate_owner_spec.spl
mirror: doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/arch/duplicate_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/arch/duplicate_owner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/arch/duplicate_owner_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/arch/duplicate_owner_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes the kernel contract at ABI v1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/arch/duplicate_owner_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every frozen canonical owner exists on disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/arch/duplicate_owner_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the production status ledger names the core subsystem owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
