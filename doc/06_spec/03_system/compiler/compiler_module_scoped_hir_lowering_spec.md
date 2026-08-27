# Compiler Module-Scoped HIR Lowering

> System-level regression check for FR-COMPILER-004. Each module must receive a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Module-Scoped HIR Lowering

System-level regression check for FR-COMPILER-004. Each module must receive a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_module_scoped_hir_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-COMPILER-004. Each module must receive a
fresh HIR lowerer with an isolated symbol table and shared import context.

## Scenarios

### compiler module-scoped HIR lowering

#### creates a fresh symbol table for each module

- creates a fresh symbol table for each module
   - Expected: second.module_filename equals `b.spl`
   - Expected: second.symbols.next_symbol_id equals `0`
   - Expected: second.module_surfaces.index_by_name.keys().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a fresh symbol table for each module")
"""A second module lowerer starts with an empty symbol table and the same module map."""
val surfaces_result = ModuleSurfacesByName.from_parts(
    [ModuleSurface.empty("synthetic")],
    {"a": 0, "b": 0}, ["a", "b"], [0, 0])
val surfaces = surfaces_result.unwrap()

var first = hirlowering_for_module("a.spl", surfaces)
first.symbols.next_symbol_id = 42

val second = hirlowering_for_module("b.spl", surfaces)
expect(second.module_filename).to_equal("b.spl")
expect(second.symbols.next_symbol_id).to_equal(0)
expect(second.module_surfaces.index_by_name.keys().len()).to_equal(2)
```

</details>

#### defers source reclamation until the streaming reparse is complete

- defers source reclamation until the streaming reparse is complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defers source reclamation until the streaming reparse is complete")
val source = file_read_text("src/compiler/80.driver/driver.spl")
expect(source).to_contain("self.ctx.source_contents_reclaimable() and not driver_streaming_surface_enabled(self.ctx)")
expect(source).to_contain("phase3:streaming_source_reclaim:done")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `5360c299e4f1677520427093f9f17e52413b9faa1877d420c066bda163e77e4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5360c299e4f1677520427093f9f17e52413b9faa1877d420c066bda163e77e4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5360c299e4f1677520427093f9f17e52413b9faa1877d420c066bda163e77e4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/compiler/compiler_module_scoped_hir_lowering_spec.spl
mirror: doc/06_spec/03_system/compiler/compiler_module_scoped_hir_lowering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/compiler_module_scoped_hir_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/compiler_module_scoped_hir_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/compiler_module_scoped_hir_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/compiler_module_scoped_hir_lowering_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a fresh symbol table for each module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_module_scoped_hir_lowering_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defers source reclamation until the streaming reparse is complete' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
