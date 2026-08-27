# Wine Kernel32 Atom Table Specification

> Tests covering Wine KERNEL32 atom table bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Atom Table Specification

## Scenarios

### Wine KERNEL32 atom table bridge

#### executes a bounded add, find, and delete atom sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded add, find, and delete atom sequence
   - Expected: result.ok is true
   - Expected: result.atom equals `0xc000`
   - Expected: result.name equals `SimpleOSWindowClass`
   - Expected: result.table.atoms.len() equals `0`
   - Expected: result.operations equals `GlobalAddAtomW GlobalFindAtomW GlobalDeleteAtom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded add, find, and delete atom sequence")
val result = wine_kernel32_execute_atom_table(
    ["GlobalAddAtomW", "GlobalFindAtomW", "GlobalDeleteAtom"],
    wine_kernel32_atom_table_new(),
    "SimpleOSWindowClass"
)

expect(result.ok).to_equal(true)
expect(result.atom).to_equal(0xc000)
expect(result.name).to_equal("SimpleOSWindowClass")
expect(result.table.atoms.len()).to_equal(0)
expect(result.operations).to_equal("GlobalAddAtomW GlobalFindAtomW GlobalDeleteAtom")
```

</details>

#### exposes direct atom table helpers

- exposes direct atom table helpers
   - Expected: added.ok is true
   - Expected: found.atom equals `0xc000`
   - Expected: deleted.ok is true
   - Expected: deleted.table.atoms.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes direct atom table helpers")
val added = wine_kernel32_global_add_atom_w(wine_kernel32_atom_table_new(), "SimpleOSWindowClass")
val found = wine_kernel32_global_find_atom_w(added.table, "SimpleOSWindowClass")
val deleted = wine_kernel32_global_delete_atom(found.table, found.atom)

expect(added.ok).to_equal(true)
expect(found.atom).to_equal(0xc000)
expect(deleted.ok).to_equal(true)
expect(deleted.table.atoms.len()).to_equal(0)
```

</details>

#### keeps atom table dispatch ordered and bounded

- keeps atom table dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-atom-table-sequence-expected:GlobalAddAtomW`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps atom table dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_atom_table(
    ["GlobalFindAtomW", "GlobalAddAtomW", "GlobalDeleteAtom"],
    wine_kernel32_atom_table_new(),
    "SimpleOSWindowClass"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-atom-table-sequence-expected:GlobalAddAtomW")

val wrong_family = wine_kernel32_execute_atom_table(
    ["GlobalAddAtomW", "GlobalFindAtomW", "HeapAlloc"],
    wine_kernel32_atom_table_new(),
    "SimpleOSWindowClass"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid atom names and ids

- rejects invalid atom names and ids
   - Expected: wine_kernel32_global_add_atom_w(table, "").error equals `GlobalAddAtomW:invalid-name`
   - Expected: wine_kernel32_global_find_atom_w(table, "MissingClass").error equals `GlobalFindAtomW:not-found`
   - Expected: wine_kernel32_global_delete_atom(table, 0xc000).error equals `GlobalDeleteAtom:invalid-atom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid atom names and ids")
val table = wine_kernel32_atom_table_new()
expect(wine_kernel32_global_add_atom_w(table, "").error).to_equal("GlobalAddAtomW:invalid-name")
expect(wine_kernel32_global_find_atom_w(table, "MissingClass").error).to_equal("GlobalFindAtomW:not-found")
expect(wine_kernel32_global_delete_atom(table, 0xc000).error).to_equal("GlobalDeleteAtom:invalid-atom")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_atom_table_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 atom table bridge.
- Wine KERNEL32 atom table bridge

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `203aa968c0ff39d8f3623a9d860423793a27c26a0247b7f5c1b83f9ce4070e42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `203aa968c0ff39d8f3623a9d860423793a27c26a0247b7f5c1b83f9ce4070e42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `203aa968c0ff39d8f3623a9d860423793a27c26a0247b7f5c1b83f9ce4070e42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_kernel32_atom_table_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_atom_table_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_atom_table_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_atom_table_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_atom_table_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_atom_table_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded add, find, and delete atom sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_atom_table_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes direct atom table helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_atom_table_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps atom table dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
