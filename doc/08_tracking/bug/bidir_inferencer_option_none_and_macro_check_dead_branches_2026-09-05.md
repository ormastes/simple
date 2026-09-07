# bidirectional_inferencer uses undeclared `Option.None`; macro_check error paths reference nonexistent symbols and infinite-loop

**Date:** 2026-09-05
**Found by:** sspec score-80 wave 9B (modernizing `test/unit/compiler/type_inference/bidir_check_spec.spl` and `test/unit/compiler/macros/macro_check_spec.spl`)

## 1. bidirectional_inferencer.spl is unrunnable

`src/compiler/30.types/bidirectional_inferencer.spl:39,64` construct
`Option.None`, but the `Option` enum in scope declares the variant `None_`.
Any load of the module's scenarios dies semantically, so the inferencer
scenarios in `bidir_check_spec.spl` pin the shipped branch text via
source-contracts instead of executing them.

## 2. macro_check dead branches (test/unit/compiler/macros/macro_check_spec.spl NOTEs)

Direct calls into these `src/compiler` macro-checker paths hang or die
semantically:

- error pushes construct `TemplateError.at` static that does not exist
- the repetition branch reads nonexistent `has_sep`
- `check_rule` / `infer_expansion_type` call missing `FragmentKind.to_text`
- `try_match_rule` returns nil against its non-optional contract
- **`check_shadowing`'s parent walk infinite-loops** — the root scope's
  parent defaults to `0`, so walking up from a root-level binding never
  terminates

The spec pins each branch via source-contract with a NOTE; the spec itself
is green (41/41) on the surface contracts.

## 3. Seed defect hit while probing

Bind-root/enter-child/resolve trips `semantic: 'marks' on Option` —
scenario bodies route around it with equivalent live calls plus
source-contract.

## Unblock condition

- `Option.None` in bidirectional_inferencer.spl renamed to the declared
  `None_` (or the enum variant renamed to `None`), module loads, and the
  inferencer scenarios in `bidir_check_spec.spl` can be re-pointed at real
  inference calls.
- The five macro_check defects above fixed; then their source-contract
  scenarios can become direct-call scenarios. The `check_shadowing`
  infinite loop is the most severe (a hang, not just a semantic error).
