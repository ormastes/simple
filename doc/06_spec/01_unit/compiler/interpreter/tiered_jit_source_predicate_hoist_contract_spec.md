# Tiered JIT source predicate hoisting contract

This structural specification guards the one-pass implementation boundary for
the tiered-JIT lexical scanner. It is intentionally source-scoped: behavioral
parity is covered by the hotspot fact specification and operation counts by the
performance specification.

## Scope and evidence

| Field | Value |
|---|---|
| Source | `test/01_unit/compiler/interpreter/tiered_jit_source_predicate_hoist_contract_spec.spl` |
| Importance | critical (weight 3), high (weight 2) |
| Oracle | owning function regions and call counts |
| Timing oracle | none |

## Contract

- `_jit_hotspot_source_scan(profile.source)` occurs once, after the typed-MIR
  and safe-deopt eligibility guard.
- The scanner has one outer cursor loop and performs no `source.contains(...)`;
  the fact-build region performs no direct source rescans.
- `jit_hotspot_backend_plugin_facts` delegates once to the private build and
  returns its value-returned `.facts` field.
- The obsolete `_with_shared` and direct rescanning helper family is absent.

These checks reject a counter-only implementation that secretly retains a
second source scan.
