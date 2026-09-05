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

---

## 2026-08-07 update — WP-A landed in the pure-Simple frontend; the pilot spec stays RED for a DIFFERENT, structural reason

**Status: partially resolved.** `resource` + `@sffi(...)` now parse in the
pure-Simple frontend. What did NOT change, and cannot change from the
pure-Simple layer, is the pilot spec.

### What landed

- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`
  - `current_ident_is_resource_decl()` — soft-keyword lookahead, cloned from
    the `layer`/`cli` precedent in the same file. `resource` is **not** a
    lexer token and **not** reserved; the WP-0 plan step "add token 222" was
    **not** taken and should be struck from the plan (see "Design/plan
    corrections" below).
  - `parse_resource_decl()` — parses `resource Name`, requires a preceding
    `@sffi`, requires `prefix:`, pre-registers the type via
    `named_type_register`, lowers to an inert `__resource_decl(name,
    meta_csv)` marker (the `__layer_decl` trick).
  - `@sffi` decorator arm — captures the closed 7-key schema (`prefix`,
    `handle`, `invalid`, `retain`, `release`, `sharing`, `thread_safe`);
    unknown key = hard parse error. `parse_sffi_arg_value()` handles string,
    ident, int, bool and a **leading minus** (`invalid: -1` is two tokens).
  - `parser_reset_pending_sffi()` wired into the per-decl pending reset so an
    `@sffi` cannot leak onto a later `resource`.
- `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` — drops the
  `__resource_decl` marker (zero HIR/MIR/codegen; WP-A excludes lowering).
- `src/compiler/90.tools/fix/rules/impl_/lint_annotation.spl` — `sffi` added
  to the known-decorator whitelist.
- `test/01_unit/compiler/resource/resource_decl_spec.spl` — **16 total, 16
  passed, 0 failed**. Verified non-vacuous by sabotage: injecting a
  `parser_error` into `parse_resource_decl` turned it red (8 hits, 4
  failures); reverting restored green.

### The structural finding (this is the important part)

`test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` is **unchanged
at `Results: 1 total, 0 passed, 1 failed`, exit 1**, before and after.

**Why: `bin/simple test` re-execs a child Rust *seed* binary, and the seed's
parser is what reads a spec file's own module-level syntax.** The error text
`Unexpected token: expected Fn, found Identifier { name: "resource", pattern:
Immutable }` is Rust `Debug` formatting from
`src/compiler_rust/parser/src/error.rs:73` — not the pure-Simple parser.

Control probe proving this is the harness and not the implementation: a spec
file containing `layer ProbeLayer` — an **already-landed, working**
pure-Simple soft keyword — fails the same way (`error[E1002]: function
`layer` not found`). No pure-Simple frontend change can alter how a spec
file's own declarations parse.

**Consequence:** the pilot spec does **not** unblock on WP-A, and does not
unblock on WP-H either. It unblocks on **stage-3 self-host** (separately
tracked), or on a seed-parser change (out of scope: "fix the pure-Simple
layer, not Rust"). Left RED and unweakened per `.claude/rules/testing.md`.

The reachable oracle for any pure-Simple frontend work is the
`test/01_unit/compiler/parser/const_spec.spl` shape: feed a **source string**
to `parse_module_body()` and assert on `module_get_decls()`. That runs the
edited `.spl` under the interpreter. `resource_decl_spec.spl` uses it.

### Design/plan corrections found while implementing

1. **Plan WP-0, "the new token is 222" — wrong and harmful.** `layer`/`cli`
   are pure `par_kind_get() == TOK_IDENT and par_text_get() == "..."` +
   lookahead predicate, with no token constant. That is the smallest change
   and makes breaking the identifier uses structurally impossible.
2. **Plan WP-A acceptance ("write `resource File` in a spec") is
   unreachable** — see the structural finding above. Every WP in the plan
   that states a spec-file-source acceptance criterion inherits this error.
3. **Plan WP-0's ~13-site wire-point checklist is not needed for WP-A.** The
   inert-marker path (`__layer_decl` precedent) carries the metadata with two
   edits. WP-C builds a real carrier when it needs one downstream.
4. **Design §1's `@sffi` schema is implementable as written**; the only gap
   is that `invalid: -1` is lexed as two tokens, which the schema prose does
   not mention.
5. Measured **112** identifier uses of `resource` in `src/**/*.spl` (regex
   over `var|val resource`, `resource:`, `resource =`, `.resource`), against
   the plan's stated 115. Raw word-occurrence count is 905 — that larger
   number includes comments and `resource_*` compound identifiers.

### Remaining open work (unchanged)

WP-B (`*R`/`@R`/`-R` sigils — note `*T` in type-annotation position **already
parses** today, verified by probe), WP-C (HIR carrier), WP-E (MIR drop
edges), WP-G (borrow enforcement), WP-H (generated adapters).

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: THE SPECS OWN PROSE IS STALE — WP-A has landed.**

`test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` lines 15-24 assert
that "as of 2026-08-07, `resource` is not a parsed declaration kind anywhere in
`src/compiler/10.frontend/**`" and that "a repo-wide grep for
`parse_resource_decl` ... returns zero hits outside the design docs".

That is no longer true. `grep -rn "parse_resource_decl" src/compiler`:

- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:230` — `fn parse_resource_decl(loop_index: i64) -> i64:` (the definition)
- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:516` — wired via `finalize_decl_visibility(parse_resource_decl(loop_index), visibility)`
- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:795` — `val res_d = parse_resource_decl(i)`
- `src/compiler/10.frontend/resource_registry.spl:40` — cross-reference

The same file carries an explicit `# ===== WP-A: resource declarations +
@sffi(...) attribute =====` banner at line 152 documenting `resource` as a
contextual (soft) keyword, exactly as the design specified.

The spec header must be rewritten before any conclusion is drawn from a RED
run: a reader currently attributes the failure to an unimplemented parser that
is in fact implemented. The remaining structural cause (if the pilot is still
RED) is downstream of parsing and has not been isolated here — see the
Unproven section.
