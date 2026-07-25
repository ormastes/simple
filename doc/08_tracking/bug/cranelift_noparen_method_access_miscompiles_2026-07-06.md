# Cranelift miscompiles zero-arg method access without parentheses on structs

## Status
Open.

## Severity
High — silent wrong-code generation; bit-test logic produces inverted results.

## Summary
Zero-argument method access WITHOUT parentheses on a struct field miscompiles under native cranelift x86_64-unknown-none. Calling `flags.present` (no parens) reads FALSE while `flags.user` reads TRUE, when both bits are set in the underlying flags word. Explicit `flags.present()` (with parens) produces correct results.

Observed in: VmFlags bit-test logic at `src/os/kernel/memory/vmm.spl` (pre-commit 059b5324), where `_flags_to_pte_bits` miscompiled leaf PTE bits, dropping PRESENT and corrupting USER, causing #PF e=0004 at CPL3.

## Evidence
- **Failure site**: `src/os/kernel/memory/vmm.spl _flags_to_pte_bits` — property-style `flags.present` read FALSE, `flags.user` read TRUE; leaf PTE 0x...004 (USER set, PRESENT dropped).
- **Discovery commits**: 12bddd3d29a1, 074fa56278f1 — ring-3 USEROK smoke triggers miscompile.
- **Workaround**: use explicit `flags.present()` with parentheses instead of property syntax.
- **Repro anchor**: vmm.spl rev pre-059b5324; struct VmFlags with present/user/writable bit methods.

## Failure Scenario
Ring-3 page fault #PF e=0004 CR2=<unmapped> — kernel tried to jump into unmapped code because PRESENT bit was dropped from leaf PTE while USER bit remained set. User-mode execution became possible on unmapped page, triggering fault.

## Impact
Any bit-flag struct using zero-arg method access for bit tests may silently produce wrong results. Blocks ring-3 OS smoke from executing.

## Next Step
Investigate cranelift lowering of property-syntax method calls (no parens). Compare generated code vs. explicit-paren version. File cranelift issue or fix in Simple compiler's HIR→MIR lowering for property-access desugaring.
