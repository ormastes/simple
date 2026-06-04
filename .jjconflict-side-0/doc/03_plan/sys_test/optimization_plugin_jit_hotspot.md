# Optimization Plugin JIT Hotspot System Test Plan

## Scope

Verify that Simple Optimization Plugin applies to JIT hotspot optimization, not
only compiler optimization. The system spec covers provider metadata, runtime
fact gating, hotspot plan eligibility, specialization-source selection, and
fallback when semantic proof is missing.

## System Spec

`test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl`

## Execution

```bash
bin/simple check test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl
bin/simple test test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl --mode=interpreter
```

## Pass Criteria

- The spec loads and checks successfully.
- The provider is `JitHotspot`, hot path, and runtime-hotspot classified.
- Required runtime facts allow the provider to run only when present.
- Eligible plans with semantic proof select specialized source.
- Missing semantic proof preserves original-source fallback.

## Traceability

| Requirement | Coverage |
|-------------|----------|
| REQ-OPJH-001 | First-class `JitHotspot` provider kind |
| REQ-OPJH-002 | Provider metadata contract |
| REQ-OPJH-003 | Built-in provider representation |
| REQ-OPJH-004 | Required runtime fact gating |
| REQ-OPJH-007 | `profile.hot_count` from tiered JIT profile |
| REQ-OPJH-009 | Fallback-preserving plan behavior |
| REQ-OPJH-011 | Promotion-time compile decision |
| REQ-OPJH-012 | Semantic-proof-gated specialization |
| REQ-OPJH-013 | Var reassignment plans require SSA, escape, and borrow safety facts |
| REQ-OPJH-014 | Cranelift tier-1 and LLVM tier-2 rebuild policy |
| REQ-OPJH-015 | MIR analyzer derives JIT var facts from reassignment, escape, and borrow evidence |
| REQ-OPJH-016 | Straight-line SSA var transform plus explicit phi-needed rejection |
| REQ-OPJH-017 | Branch-merge phi requirement diagnostics include affected locals |
| REQ-OPJH-018 | Branch-merge phi insertion plans include join, branch values, and destination |
| REQ-OPJH-019 | Branch-merge phi materialization uses pseudo-phi MIR intrinsic |
| REQ-OPJH-020 | Interpreter consumes pseudo-phi MIR intrinsic deterministically |
| NFR-OPJH-008 | Missing proof degrades to original-source compilation |
