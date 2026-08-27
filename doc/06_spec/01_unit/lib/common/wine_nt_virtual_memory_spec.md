# Wine Nt Virtual Memory Specification

> Tests covering Wine NT virtual memory bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Virtual Memory Specification

## Scenarios

### Wine NT virtual memory bridge

#### lists the modeled VirtualAlloc, VirtualProtect, and VirtualFree calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists the modeled VirtualAlloc, VirtualProtect, and VirtualFree calls
   - Expected: calls.len() equals `3`
   - Expected: calls[0] equals `VirtualAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lists the modeled VirtualAlloc, VirtualProtect, and VirtualFree calls")
val calls = wine_nt_virtual_memory_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("VirtualAlloc")
```

</details>

#### allocates automatic committed memory through the VM adapter

- allocates automatic committed memory through the VM adapter
   - Expected: allocated.ok is true
   - Expected: allocated.state equals `allocated`
   - Expected: allocated.base equals `0x10000000`
   - Expected: wine_vm_access_gate(allocated.space, allocated.base, "write") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allocates automatic committed memory through the VM adapter")
val allocated = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0, 0x2000, "rw")
expect(allocated.ok).to_equal(true)
expect(allocated.state).to_equal("allocated")
expect(allocated.base).to_equal(0x10000000)
expect(wine_vm_access_gate(allocated.space, allocated.base, "write")).to_equal("ready")
```

</details>

#### allocates fixed memory and rejects fixed overlap

- allocates fixed memory and rejects fixed overlap
   - Expected: first.ok is true
   - Expected: second.ok is false
   - Expected: second.state equals `fixed-map-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allocates fixed memory and rejects fixed overlap")
val first = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0x400000, 0x2000, "rw")
val second = wine_nt_virtual_memory_alloc(first.space, 0x401000, 0x1000, "rw")
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(false)
expect(second.state).to_equal("fixed-map-conflict")
```

</details>

#### protects committed memory and returns old permissions

- protects committed memory and returns old permissions
   - Expected: protected.ok is true
   - Expected: protected.state equals `protected`
   - Expected: protected.old_perms equals `rw`
   - Expected: wine_vm_access_gate(protected.space, 0x500000, "execute") equals `ready`
   - Expected: wine_vm_access_gate(protected.space, 0x500000, "write") equals `page-fault-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("protects committed memory and returns old permissions")
val allocated = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0x500000, 0x1000, "rw")
val protected = wine_nt_virtual_memory_protect(allocated.space, 0x500000, "rx")
expect(protected.ok).to_equal(true)
expect(protected.state).to_equal("protected")
expect(protected.old_perms).to_equal("rw")
expect(wine_vm_access_gate(protected.space, 0x500000, "execute")).to_equal("ready")
expect(wine_vm_access_gate(protected.space, 0x500000, "write")).to_equal("page-fault-write")
```

</details>

#### frees mapped memory through the VM adapter

- frees mapped memory through the VM adapter
   - Expected: freed.ok is true
   - Expected: freed.state equals `freed`
   - Expected: wine_vm_access_gate(freed.space, 0x600000, "read") equals `page-fault-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("frees mapped memory through the VM adapter")
val allocated = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0x600000, 0x1000, "rw")
val freed = wine_nt_virtual_memory_free(allocated.space, 0x600000)
expect(freed.ok).to_equal(true)
expect(freed.state).to_equal("freed")
expect(wine_vm_access_gate(freed.space, 0x600000, "read")).to_equal("page-fault-unmapped")
```

</details>

#### rejects invalid allocation and missing protect/free targets

- rejects invalid allocation and missing protect/free targets
   - Expected: wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0, 0, "rw").state equals `invalid-size`
   - Expected: wine_nt_virtual_memory_protect(wine_vm_space_new(), 0x700000, "rx").state equals `missing-region`
   - Expected: wine_nt_virtual_memory_free(wine_vm_space_new(), 0x700000).state equals `missing-region`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid allocation and missing protect/free targets")
expect(wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0, 0, "rw").state).to_equal("invalid-size")
expect(wine_nt_virtual_memory_protect(wine_vm_space_new(), 0x700000, "rx").state).to_equal("missing-region")
expect(wine_nt_virtual_memory_free(wine_vm_space_new(), 0x700000).state).to_equal("missing-region")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NT virtual memory bridge.
- Wine NT virtual memory bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `47fad2027ef9c385b9f43ab25843af0bcee33d32678e0c51f14ba5eb38ba8178`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47fad2027ef9c385b9f43ab25843af0bcee33d32678e0c51f14ba5eb38ba8178`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47fad2027ef9c385b9f43ab25843af0bcee33d32678e0c51f14ba5eb38ba8178`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_nt_virtual_memory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_nt_virtual_memory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_nt_virtual_memory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists the modeled VirtualAlloc, VirtualProtect, and VirtualFree calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates automatic committed memory through the VM adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates fixed memory and rejects fixed overlap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
