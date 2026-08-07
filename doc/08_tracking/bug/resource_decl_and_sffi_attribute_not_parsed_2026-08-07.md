# Bug: `resource` declaration + `@sffi(...)` attribute are not parsed by the real frontend at all

- **Date:** 2026-08-07
- **Status:** open
- **Severity:** medium (blocks any real-source verification of the SFFI
  ownership-migration feature; expected — this is WP-A of a tracked
  parallel-agent plan, not yet landed)
- **Found by:** SFFI resource-migration pilot session, while writing
  `test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl`

## The actual defect

`resource` is not a recognized declaration keyword anywhere in
`src/compiler/10.frontend/**`. Repo-wide grep for `parse_resource_decl` /
`DECL_RESOURCE` / `@sffi` (as a consumed attribute, not the design-doc prose)
returns zero hits in `src/compiler/`. The architecture doc
(`doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`
§5.1, "Full wire-point checklist for a new declaration kind") lists the ~13
call sites a new declaration kind must touch (`_Ast/decl_nodes.spl`,
`_ParserDecls/enum_module_body.spl`, `core/compiler/c_codegen.spl`,
`core/interpreter/eval_decls.spl`, `core/interpreter/module_loader_core.spl`,
...) — none of them exist yet. This is **WP-A** in
`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`
("Parser: `resource` decl + `@sffi` consumption"), explicitly not landed as
of this writing per that plan's own Status section.

Confirmed not landed in any live sibling session's uncommitted tree either
(checked at pilot time, 2026-08-07):
`git status --porcelain | grep -i "parser\|resource\|sffi"` showed one
uncommitted change to
`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`, but its
diff is unrelated — a `layer NAME` / `layer NAME uses A, B` soft-keyword
decl for the zero-cost-layers M0 milestone
(`doc/03_plan/compiler/forwarding/zero_cost_layers_c0_c5_staged_implementation_plan_2026-08-07.md`),
not `resource`.

Direct repro (`bin/simple test` on real module-level source text, same
interpreter path every spec loads through):

```simple
@sffi(prefix: "rt_io_file", invalid: -1)
resource File
```

```
error: compile failed: parse: in ".../resource_sffi_pilot_spec.spl": Unexpected token:
  expected Fn, found Identifier { name: "resource", pattern: Immutable }
Results: 1 total, 0 passed, 1 failed
```

The parser's module-body dispatcher has no case for a bare `resource`
identifier in declaration position (unlike `mod`/`export`, which do have
dispatch arms in
`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:parse_module_decl_with_visibility`)
— it falls through to the generic top-level-statement path, which requires a
recognized declaration keyword (`fn`, ...) and rejects the bare identifier.
`@sffi(...)` never gets a chance to run, because the token immediately after
it (`resource`) is what fails.

Separately (not the same bug, worth noting so nobody re-discovers it as a
surprise): `bin/simple lint` on the same file reports **0 errors** and loads
cleanly — lint runs through the lighter-weight treesitter/outline parser,
not `parse_full_frontend`, and currently treats `resource` as an ordinary
identifier rather than flagging it, so a green `bin/simple lint` on a
`resource`-using file is not evidence the file compiles.

## Unblock condition

WP-A lands (`resource` decl parsing + `@sffi` attribute consumption via the
existing `parse_attributes()` path, per
`doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md`
§1). Per that plan's dependency graph, WP-A also needs WP-0 (skeleton +
shared decisions) done first, and the fuller safety story
(`close()` double-release rejection, use-after-close rejection) additionally
needs WP-C (HIR lowering) → WP-E (MIR drop edges) → WP-G (borrow-check
enforcement), none of which are landed either.

## Affected spec

`test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` — intentionally
left RED (whole-file parse failure) rather than weakened to test a
hand-rolled workaround class, per `.claude/rules/testing.md`. Four pilot
families are declared there (`File`, `Image`, `CudaPrimaryContext`,
`AtomicCounter`) covering both `sharing: none`/unique-`R` and
`sharing: foreign`/`sharing: wrapper` `*R` strategies across the
`nogc_sync_mut` and `gc_async_mut` tiers.
