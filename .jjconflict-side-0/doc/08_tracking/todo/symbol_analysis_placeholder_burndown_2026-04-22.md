# symbol_analysis_placeholder_burndown

Date: 2026-04-22
Parent TODO row: 194
Status: partial fix; parent remains open

## Research

The anti-dummy backlog row is a parent tracker. The smallest actionable remaining placeholder found in the backlog scan was `test/system/compiler/symbol_analysis_spec.spl`, which had one tautological `expect(true).to_equal(true)` and no runtime gating.

## Plan

Replace the placeholder with a real symbol-analysis behavior check: create a graph through `SymbolAnalyzer`, mark `main` as the entry point, add a call edge to `helper`, leave `unused` disconnected, then verify reachability stats and removable symbol output.

## Fix

Updated `test/system/compiler/symbol_analysis_spec.spl` to assert concrete symbol analysis behavior. Row 194 remains open because it tracks the broader placeholder backlog.

## Verification

- `bin/simple lint test/system/compiler/symbol_analysis_spec.spl`
- `timeout 120s bin/simple test test/system/compiler/symbol_analysis_spec.spl`
- `rg -n 'expect\\(true\\)\\.to_equal\\(true\\)|pass_todo|pass_do_nothing|pass_dn' test/system/compiler/symbol_analysis_spec.spl`
