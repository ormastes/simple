# windows_c_compiler_selection rule misses derived-version forgeries (2026-10-30)

Status: open
Area: compiler/lint/rules/windows_c_compiler_selection_rule.spl

## Symptom

In `test/01_unit/compiler/lint/windows_c_compiler_selection_spec.spl`, 3 of 23 examples report 0
findings where 1 is expected:

- "rejects diagnostic-only version derivation": `$diagnostic = "compiler output: $version"`, then
  matches on `$diagnostic`
- "rejects a fabricated prefix joined with queried output": `$proof = "$prefix $version" -join ...`
- "rejects unknown aliases and roots without a fail-closed version predicate": the shell forms
  `CC=$CC_UNTRUSTED`, `CC=$LLVM_ROOT/...` with no probe, and a token-only `--version` call

A fourth example failed only because its CMake fixture `"${SIMPLE_WINDOWS_LLVM_ROOT}"` was
interpolated by Simple. That spec was fixed with `${{...}}`.

## Root cause

The rule and the spec both arrived in the 2026-09-29 transplant `88aac2ffe28`, and neither has any
later history. The spec describes value-flow checks (which variable the version predicate actually
tests, and whether a literal prefix was joined in) that the rule's line-pattern implementation does
not perform.

## Unblock

Add value-flow tracking for the version variable to the rule. Then remove the `pending` markers that
link here.
