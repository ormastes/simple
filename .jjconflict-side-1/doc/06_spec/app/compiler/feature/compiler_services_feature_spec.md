# Compiler Services Feature Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/compiler_services_feature_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 41 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/compiler_services_feature/result.json` |

## Scenarios

- [slow] lexer port is present
- [slow] parser port is present
- [slow] desugarer port is present
- [slow] type checker port is present
- [slow] HIR lowerer port is present
- [slow] MIR lowerer port is present
- [slow] backend port is present
- [slow] logger port is present
- [slow] module loader port is present
- [slow] all 9 ports exist in a single services container
- [slow] lexer port tokenize_fn is callable
- [slow] lexer port tokenize_fn handles empty string
- [slow] parser port parse_fn is callable
- [slow] parser port parse_fn accepts non-empty token list
- [slow] desugarer port desugar_fn is callable
- [slow] desugarer port desugar_fn passes through empty source
- [slow] type checker port check_fn is callable
- [slow] hir lowerer port lower_fn is callable
- [slow] mir lowerer port lower_fn is callable
- [slow] backend port supports_jit_fn is callable
- [slow] backend port target_triple_fn is callable
- [slow] logger port has name field
- [slow] logger port has level field
- [slow] module loader port load_fn is callable
- [slow] module loader port resolve_fn is callable
- [slow] calling create_default_services twice gives independent containers
- [slow] all ports in two independent containers share the same names
- [slow] replacing lexer port does not affect parser port name
- [slow] accessing one port does not change another port
- [slow] accessing backend port does not affect logger port
- [slow] accessing module loader does not affect hir or mir lowerers
- [slow] tokenize stage returns empty token list for noop lexer
- [slow] parse stage returns no errors for noop parser
- [slow] desugar stage returns source for noop desugarer
- [slow] type check stage returns no errors for noop checker
- [slow] HIR lowering stage returns no errors for noop lowerer
- [slow] MIR lowering stage returns no errors for noop lowerer
- [slow] backend stage reports no JIT support for noop backend
- [slow] backend stage reports noop target triple
- [slow] running through all 9 stages sequentially produces no errors
- [slow] module loader can resolve and load during pipeline
