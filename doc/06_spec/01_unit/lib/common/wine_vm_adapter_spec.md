# Wine Vm Adapter Specification

> Tests covering Wine VM adapter model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Vm Adapter Specification

## Scenarios

### Wine VM adapter model

#### detects interval overlap for fixed mappings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects interval overlap for fixed mappings
   - Expected: wine_vm_regions_overlap(100, 20, 110, 20) is true
   - Expected: wine_vm_regions_overlap(100, 20, 120, 20) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects interval overlap for fixed mappings")
expect(wine_vm_regions_overlap(100, 20, 110, 20)).to_equal(true)
expect(wine_vm_regions_overlap(100, 20, 120, 20)).to_equal(false)
```

</details>

#### reserves automatic and fixed ranges

- reserves automatic and fixed ranges
   - Expected: auto_res.ok is true
   - Expected: auto_res.region.base equals `0x10000000`
   - Expected: fixed.ok is true
   - Expected: fixed.region.base equals `0x20000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reserves automatic and fixed ranges")
val auto_res = wine_vm_reserve(wine_vm_space_new(), 0x2000)
expect(auto_res.ok).to_equal(true)
expect(auto_res.region.base).to_equal(0x10000000)

val fixed = wine_vm_reserve_fixed(auto_res.space, 0x20000000, 0x1000)
expect(fixed.ok).to_equal(true)
expect(fixed.region.base).to_equal(0x20000000)
```

</details>

#### rejects overlapping fixed mappings

- rejects overlapping fixed mappings
   - Expected: second.ok is false
   - Expected: second.state equals `fixed-map-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects overlapping fixed mappings")
val first = wine_vm_reserve_fixed(wine_vm_space_new(), 0x400000, 0x2000)
val second = wine_vm_reserve_fixed(first.space, 0x401000, 0x2000)
expect(second.ok).to_equal(false)
expect(second.state).to_equal("fixed-map-conflict")
```

</details>

#### commits and protects reserved regions

- commits and protects reserved regions
   - Expected: committed.state equals `committed`
   - Expected: protected.state equals `protected`
   - Expected: wine_vm_access_gate(protected.space, 0x500000, "execute") equals `ready`
   - Expected: wine_vm_access_gate(protected.space, 0x500000, "write") equals `page-fault-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("commits and protects reserved regions")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x500000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x500000, "rw")
expect(committed.state).to_equal("committed")
val protected = wine_vm_protect(committed.space, 0x500000, "rx")
expect(protected.state).to_equal("protected")
expect(wine_vm_access_gate(protected.space, 0x500000, "execute")).to_equal("ready")
expect(wine_vm_access_gate(protected.space, 0x500000, "write")).to_equal("page-fault-write")
```

</details>

#### writes and reads modeled bytes from committed writable VM memory

- writes and reads modeled bytes from committed writable VM memory
   - Expected: written.ok is true
   - Expected: written.operations equals `VMBytesWritten`
   - Expected: read.ok is true
   - Expected: read.operations equals `VMBytesRead`
   - Expected: read.bytes[0] equals `1`
   - Expected: read.bytes[3] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("writes and reads modeled bytes from committed writable VM memory")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x510000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x510000, "rw")
val written = wine_vm_write_bytes(committed.space, 0x510008, [1, 2, 3, 4])
expect(written.ok).to_equal(true)
expect(written.operations).to_equal("VMBytesWritten")

val read = wine_vm_read_bytes(written.space, 0x510008, 4)
expect(read.ok).to_equal(true)
expect(read.operations).to_equal("VMBytesRead")
expect(read.bytes[0]).to_equal(1)
expect(read.bytes[3]).to_equal(4)
```

</details>

#### rejects modeled byte writes that cross region bounds or write-protected pages

- rejects modeled byte writes that cross region bounds or write-protected pages
   - Expected: protected.ok is false
   - Expected: protected.state equals `page-fault-write`
   - Expected: boundary.ok is false
   - Expected: boundary.state equals `page-fault-boundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects modeled byte writes that cross region bounds or write-protected pages")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x520000, 0x10)
val committed = wine_vm_commit(reserved.space, 0x520000, "r")
val protected = wine_vm_write_bytes(committed.space, 0x520000, [1])
expect(protected.ok).to_equal(false)
expect(protected.state).to_equal("page-fault-write")

val rw = wine_vm_protect(committed.space, 0x520000, "rw")
val boundary = wine_vm_write_bytes(rw.space, 0x52000f, [1, 2])
expect(boundary.ok).to_equal(false)
expect(boundary.state).to_equal("page-fault-boundary")
```

</details>

#### reports guard and uncommitted faults

- reports guard and uncommitted faults
   - Expected: wine_vm_access_gate(reserved.space, 0x600000, "read") equals `page-fault-uncommitted`
   - Expected: wine_vm_access_gate(guarded.space, 0x600000, "read") equals `page-fault-guard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports guard and uncommitted faults")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x600000, 0x1000)
expect(wine_vm_access_gate(reserved.space, 0x600000, "read")).to_equal("page-fault-uncommitted")
val committed = wine_vm_commit(reserved.space, 0x600000, "rw")
val guarded = wine_vm_mark_guard(committed.space, 0x600000)
expect(wine_vm_access_gate(guarded.space, 0x600000, "read")).to_equal("page-fault-guard")
```

</details>

#### unmaps regions and validates user pointer lookup

- unmaps regions and validates user pointer lookup
   - Expected: wine_vm_region_contains(wine_vm_space_find(reserved.space, 0x700100), 0x700100) is true
   - Expected: unmapped.state equals `unmapped`
   - Expected: wine_vm_access_gate(unmapped.space, 0x700100, "read") equals `page-fault-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unmaps regions and validates user pointer lookup")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x700000, 0x1000)
expect(wine_vm_region_contains(wine_vm_space_find(reserved.space, 0x700100), 0x700100)).to_equal(true)
val unmapped = wine_vm_unmap(reserved.space, 0x700000)
expect(unmapped.state).to_equal("unmapped")
expect(wine_vm_access_gate(unmapped.space, 0x700100, "read")).to_equal("page-fault-unmapped")
```

</details>

#### builds fault evidence accepted by the VM fault gate

- builds fault evidence accepted by the VM fault gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds fault evidence accepted by the VM fault gate")
val evidence = wine_vm_fault_evidence(_fault())
expect(evidence).to_contain("process=10")
expect(evidence).to_contain("thread=20")
expect(evidence).to_contain("policy=deliver-seh")
```

</details>

#### derives ready VM features when mappings, guard, exec, namespaces, and fault evidence exist

- derives ready VM features when mappings, guard, exec, namespaces, and fault evidence exist
   - Expected: wine_vm_adapter_gate(guarded.space, container, _fault()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives ready VM features when mappings, guard, exec, namespaces, and fault evidence exist")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x800000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x800000, "rx")
val guarded = wine_vm_mark_guard(committed.space, 0x800000)
val container = "pid fs ipc net capability"
val features = wine_vm_adapter_feature_string(guarded.space, container)
expect(features).to_contain("exec-perm")
expect(features).to_contain("guard-page")
expect(features).to_contain("cap-namespace")
expect(wine_vm_adapter_gate(guarded.space, container, _fault())).to_equal("ready")
```

</details>

#### does not derive namespace features from container substring collisions

- does not derive namespace features from container substring collisions
   - Expected: features does not contain `pid-namespace`
   - Expected: features does not contain `fs-namespace`
   - Expected: features does not contain `ipc-namespace`
   - Expected: features does not contain `net-namespace`
   - Expected: features does not contain `cap-namespace`
   - Expected: wine_vm_adapter_gate(guarded.space, container, _fault()) equals `missing-pid-namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not derive namespace features from container substring collisions")
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x810000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x810000, "rx")
val guarded = wine_vm_mark_guard(committed.space, 0x810000)
val container = "stupid xfs epic ethernet incapability"
val features = wine_vm_adapter_feature_string(guarded.space, container)
expect(features.contains("pid-namespace")).to_equal(false)
expect(features.contains("fs-namespace")).to_equal(false)
expect(features.contains("ipc-namespace")).to_equal(false)
expect(features.contains("net-namespace")).to_equal(false)
expect(features.contains("cap-namespace")).to_equal(false)
expect(wine_vm_adapter_gate(guarded.space, container, _fault())).to_equal("missing-pid-namespace")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_vm_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine VM adapter model.
- Wine VM adapter model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `54484f9888964d298ed21c82d460620b38300ca6f1e66b46fcfacc63d4e55135`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54484f9888964d298ed21c82d460620b38300ca6f1e66b46fcfacc63d4e55135`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54484f9888964d298ed21c82d460620b38300ca6f1e66b46fcfacc63d4e55135`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_vm_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_vm_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_vm_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_vm_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_vm_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_vm_adapter_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects interval overlap for fixed mappings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_vm_adapter_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves automatic and fixed ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_vm_adapter_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overlapping fixed mappings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
