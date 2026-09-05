# HIR Function Count Unit Spec

> Uses the native-safe dictionary key-array count path required by Stage4.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR Function Count Unit Spec

Uses the native-safe dictionary key-array count path required by Stage4.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/hir_function_count_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Uses the native-safe dictionary key-array count path required by Stage4.

`driver_dict_entry_count` is deliberately NOT generic: the native build path
has no monomorphization (#158 Phase B), so a `<K, V>` signature is a hard stop
for Stage-3 self-host. It therefore takes the one instantiation the driver
actually uses, `Dict<SymbolId, HirFunction>`, and this spec exercises it at
that exact type rather than at a convenience type the production path never
passes.

## Scenarios

### driver native dictionary count

#### counts an empty function table without direct Dict len

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts an empty function table without direct Dict len
   - Expected: driver_dict_entry_count(entries) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts an empty function table without direct Dict len")
val entries: Dict<SymbolId, HirFunction> = {}
expect(driver_dict_entry_count(entries)).to_equal(0)
```

</details>

#### counts a populated function table through its typed keys

- counts a populated function table through its typed keys
   - Expected: driver_dict_entry_count(entries) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts a populated function table through its typed keys")
var entries: Dict<SymbolId, HirFunction> = {}
entries[SymbolId(id: 1)] = stub_hir_function(1, "main")
entries[SymbolId(id: 2)] = stub_hir_function(2, "helper")
expect(driver_dict_entry_count(entries)).to_equal(2)
```

</details>

#### tracks replacement without inflating the entry count

- tracks replacement without inflating the entry count
   - Expected: driver_dict_entry_count(entries) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks replacement without inflating the entry count")
var entries: Dict<SymbolId, HirFunction> = {}
entries[SymbolId(id: 1)] = stub_hir_function(1, "main")
entries[SymbolId(id: 1)] = stub_hir_function(1, "main_redefined")
expect(driver_dict_entry_count(entries)).to_equal(1)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8364daa361ade5d04b9f53951552a9fa7d57a82b495a7fe34ce0ce1f8fa58d47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8364daa361ade5d04b9f53951552a9fa7d57a82b495a7fe34ce0ce1f8fa58d47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8364daa361ade5d04b9f53951552a9fa7d57a82b495a7fe34ce0ce1f8fa58d47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/driver/hir_function_count_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/hir_function_count_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/hir_function_count_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/hir_function_count_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/hir_function_count_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/hir_function_count_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts an empty function table without direct Dict len' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/hir_function_count_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts a populated function table through its typed keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/hir_function_count_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks replacement without inflating the entry count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
