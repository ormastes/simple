# Symbol Analysis Specification

> _Reachability and dead-symbol behavior for linker symbol analysis._

<!-- sdn-diagram:id=symbol_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbol_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbol_analysis_spec -> std
symbol_analysis_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbol_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Analysis Specification

## Scenarios

### Symbol Analysis
_Reachability and dead-symbol behavior for linker symbol analysis._

#### marks entry-point references reachable and reports dead symbols

1. var analyzer = SymbolAnalyzer create
2. analyzer add symbol
3. analyzer add symbol
4. analyzer add symbol
5. analyzer add reference
6. analyzer set entry point
7.   = analyzer analyze
   - Expected: stats.total_symbols equals `3`
   - Expected: stats.reachable_symbols equals `2`
   - Expected: stats.dead_symbols equals `1`
   - Expected: stats.dead_size equals `16`
   - Expected: stats.total_size equals `112`
   - Expected: removable.len() equals `1`
   - Expected: removable[0] equals `unused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var analyzer = SymbolAnalyzer.create()
analyzer.add_symbol("main", SymbolVisibility.Export, 64, ".text")
analyzer.add_symbol("helper", SymbolVisibility.Local, 32, ".text")
analyzer.add_symbol("unused", SymbolVisibility.Local, 16, ".text")
analyzer.add_reference("main", "helper", RefKind.Call)
analyzer.set_entry_point("main")

_ = analyzer.analyze()

val stats = analyzer.stats()
expect(stats.total_symbols).to_equal(3)
expect(stats.reachable_symbols).to_equal(2)
expect(stats.dead_symbols).to_equal(1)
expect(stats.dead_size).to_equal(16)
expect(stats.total_size).to_equal(112)

val removable = analyzer.get_removable_symbols()
expect(removable.len()).to_equal(1)
expect(removable[0]).to_equal("unused")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/symbol_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Symbol Analysis

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
