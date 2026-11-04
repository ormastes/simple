# Frozen stage2 rejects `nil` in an optional enum-payload slot; `None` is a STAGE2 WORKAROUND, not the target spelling

- **ID:** stage2_rejects_nil_in_optional_enum_payload_2026-11-05
- **Priority:** P2 (bootstrap-only: the frozen stage2 that builds stage3 refuses the canonical spelling; the seed accepts it)
- **Status:** open. Workaround sites carry `@workaround bug=stage2_rejects_nil_in_optional_enum_payload_2026-11-05`.
- **Policy:** the final design (scratchpad `panic_free_rev3_decisions.md`, ERR-01) makes `nil` the ONLY canonical absence literal, with no competing `None`. Every `None` written for this bug is therefore temporary and must be restored to `nil` once stage3 self-hosts (i.e. once the compiler that builds the next stage accepts `nil` here).

## Symptom
PR #6707 added `HirTypeKind.Array(int_elem, nil)` / `HirTypeKind.Array(float_elem, nil)` in
`src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl` (`builtin_remember_array_literal_init`). The seed
compiled it and the spec passed (7/7). The frozen stage2 (phase-3 lane, p3-envpol MIR leaf) rejected it:

```
builtin_method_extras.spl:827/830: nil outside unsafe into optional payload slot (declared 'i64?'); use None
```

PR #6757 changed both sites to `None` (the spelling release already uses at `expression_core.spl:628/633`).

## Lesson (recorded for the fix lanes)
A seed-green spec does NOT prove the frozen stage2 accepts `nil` in an optional enum-payload slot. Until stage3
self-hosts, spell such slots `None` and tag the site with this bug id so the sites can be swept back to `nil`.

## Restore recipe
`git grep -n 'bug=stage2_rejects_nil_in_optional_enum_payload_2026-11-05'` lists every site; replace the `None`
on the following line by `nil`, drop the tag, re-run the owning spec, and close this row.

## Sites
- `src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl` (2 sites, `Array(int_elem|float_elem, None)`)
- Sibling scan 2026-11-05 over every file merged by the fix lane that day found no other bare-nil enum-payload literal;
  pre-existing `None` spellings elsewhere (e.g. `expression_core.spl:628/633`) are not tagged by this row.
