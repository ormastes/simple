# CompilerServices Pipeline Stage Ports

**Feature ID:** #BACKEND-003 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/app/compiler_services_feature_spec.spl`_

---

## Overview

Tests the Pipeline Stage Ports feature for CompilerServices across four phases. Phase 1 verifies
all 9 ports (lexer, parser, desugarer, type checker, HIR lowerer, MIR lowerer, backend, logger,
module loader) are present with correct names. Phase 2 confirms each port's function fields are
callable. Phase 3 validates port replacement independence. Phase 4 runs a full pipeline simulation
through all 9 stages sequentially, ensuring no errors from noop implementations.

## Syntax

```simple
val svc = create_default_services()
expect(svc.lexer.name).to_equal("noop-lexer")
expect(svc.parser.name).to_equal("noop-parser")

val lf = svc.lexer.tokenize_fn
val tokens = lf("fn main(): print 1")
expect(tokens.len()).to_equal(0)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 43 |

## Test Structure

### CompilerServices Feature: Phase 1 - All ports present

- ✅ lexer port is present
- ✅ parser port is present
- ✅ desugarer port is present
- ✅ type checker port is present
- ✅ HIR lowerer port is present
- ✅ MIR lowerer port is present
- ✅ backend port is present
- ✅ logger port is present
- ✅ module loader port is present
- ✅ all 9 ports exist in a single services container
### CompilerServices Feature: Phase 2 - Each port callable

- ✅ lexer port tokenize_fn is callable
- ✅ lexer port tokenize_fn handles empty string
- ✅ parser port parse_fn is callable
- ✅ parser port parse_fn accepts non-empty token list
- ✅ desugarer port desugar_fn is callable
- ✅ desugarer port desugar_fn passes through empty source
- ✅ type checker port check_fn is callable
- ✅ hir lowerer port lower_fn is callable
- ✅ mir lowerer port lower_fn is callable
- ✅ backend port supports_jit_fn is callable
- ✅ backend port target_triple_fn is callable
- ✅ logger port debug_fn is callable
- ✅ logger port info_fn is callable
- ✅ logger port warn_fn is callable
- ✅ logger port error_fn is callable
- ✅ module loader port load_fn is callable
- ✅ module loader port resolve_fn is callable
### CompilerServices Feature: Phase 3 - Port replacement

- ✅ calling create_default_services twice gives independent containers
- ✅ all ports in two independent containers share the same names
- ✅ replacing lexer port does not affect parser port name
- ✅ accessing one port does not change another port
- ✅ accessing backend port does not affect logger port
- ✅ accessing module loader does not affect hir or mir lowerers
### CompilerServices Feature: Phase 4 - Full pipeline simulation

- ✅ tokenize stage returns empty token list for noop lexer
- ✅ parse stage returns no errors for noop parser
- ✅ desugar stage returns source for noop desugarer
- ✅ type check stage returns no errors for noop checker
- ✅ HIR lowering stage returns no errors for noop lowerer
- ✅ MIR lowering stage returns no errors for noop lowerer
- ✅ backend stage reports no JIT support for noop backend
- ✅ backend stage reports noop target triple
- ✅ running through all 9 stages sequentially produces no errors
- ✅ module loader can resolve and load during pipeline

