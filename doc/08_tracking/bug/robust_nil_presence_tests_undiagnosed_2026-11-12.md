# Raw `case nil:` and `== nil` in safe code are not diagnosed (S-11)

**Status:** OPEN 2026-11-12 — design P2+ work; the acceptance spec is RED by design.
**Severity:** Warning-tier policy gap (no runtime defect).
**Affected file:** `src/compiler/90.tools/lint/rules/nil_outside_unsafe_rule.spl:103-108` (`nil_lint_is_presence_test` skips `== nil`, `!= nil`, `case nil`, `| nil`).
**Spec files:** `test/01_unit/compiler/semantics/robust_nil_pattern_spec.spl:28-37` (reproducing: pattern + comparison), `test/01_unit/compiler/lint/nil_outside_unsafe_rule_spec.spl:49-52` (generalization; currently asserts the opposite and must flip with the fix).
**Design:** `doc/05_design/language/robust_types/robust_types_layer_contracts_2026-11-12.md` §2 Rule G, §7 `NIL-UNSAFE-001`, §9 S-11.

## Symptom

`NIL-UNSAFE-001` deliberately leaves presence tests alone because natively
`None` is an Option object and `nil` the word 3, so a mechanical
`x != nil` -> `x != None` rewrite changes behaviour. The design keeps that
constraint (no mechanical rewrite) but still requires the raw `nil` to be
diagnosed, with a typed replacement (`.?`, `if val`, `case None`) chosen
from resolved semantics.

## Unblock condition

Emit `NIL-UNSAFE-001` on `case nil:` and `== nil` / `!= nil` outside
`unsafe:` with a hint that names the typed replacement rather than `None`
text substitution; then flip the "leaves presence tests alone" block of the
generalization spec. Belongs to design phase P2 (source `nil` vs omitted
initializer split) — not P0/P1.
