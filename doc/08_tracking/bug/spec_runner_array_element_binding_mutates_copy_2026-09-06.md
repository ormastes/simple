# Spec runner: mutating an array element through a binding writes a copy (differs from `simple run`)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-06 · **Status:** OPEN · **Found by:** slim-UI lane A04 (Tiny layout), seed `src/compiler_rust/target/bootstrap/simple`

## Symptom

```simple
val n = s.nodes[2]
n.parent = 7          # under the spec runner (`it` bodies AND module fns called from them): writes a COPY
                      # under `simple run script.spl`: mutates s.nodes[2] in place
s.nodes[2] = TinyGuiNode(...)   # whole-element assign works in both
s.nodes[0].value = 1            # semantic: invalid assignment: complex indexed field receiver is not supported
```

## Consequence

Specs that "mutate a node then re-render" can be silent no-ops under `simple test`/spec
mode while passing under `run`. Likely affected today: `test/01_unit/lib/tiny/tui_render_spec.spl`
(`checked.value = 1`, `list.value = 1`). Same family as
`doc/08_tracking/bug/nested_array_element_bound_to_var_copies_2026-09-05.md` (run path);
this record pins the spec-runner divergence and the unsupported indexed-field receiver.

## Unblock

Two specs per `.claude/rules/testing.md`: one reproducing the binding-copy divergence
(same source, `run` vs spec runner), one for the `s.nodes[0].value = 1` semantic error.
Fix in the pure-Simple interpreter's assignment lowering; until then Tiny specs use
whole-element assignment (`s.nodes[i] = TinyGuiNode(...)`) and say so.

