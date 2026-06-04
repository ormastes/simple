# SimpleOS/QEMU CLibParityHotspot Evidence - 2026-05-26

## Scope

Implemented the optimization-plugin item from
`doc/03_plan/simpleos_real_hw_qemu_consolidated_plan_2026-05-26.md`: SimpleOS
and QEMU hot paths use the general `CLibParityHotspot` parity-provider rules
instead of a runner-specific optimizer.

## Implementation

- `src/compiler/60.mir_opt/mir_opt/pattern/rules_clib_parity.spl`
  - Added `CLibParityRewriteDecision`.
  - Added `clib_parity_rule_rewrite_decision(...)`.
  - Added `clib_parity_rule_can_rewrite(...)`.
  - Added `clib_parity_rule_by_name(...)`.
- The same eligibility helper checks required facts and required proofs for
  general filesystem, database, webserver, and SimpleOS/QEMU rules.
- SimpleOS/QEMU rules remain limited to:
  - volatile ordering preservation for bounded MMIO polling
  - marker-contract preservation for serial marker scanning
  - fail-closed equivalence for provider grant checks

## Verification

Command:

```bash
src/compiler_rust/target/debug/simple test test/compiler/mir_opt/clib_parity_hotspot_spec.spl --mode=interpreter
```

Result:

- Passed: 19
- Failed: 0

