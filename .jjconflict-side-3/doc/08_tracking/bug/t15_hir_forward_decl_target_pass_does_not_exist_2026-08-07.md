# T15 blocked: no "HIR-lowering site" exists for `HirForwardDecl` to wire into — the target pass is dead code with zero production users

- **Status:** BLOCKED — honest gate report, not implemented. Scoped down to a
  characterization spec only (see "What was landed" below).
- **Found:** 2026-08-07, executing plan unit T15 from
  `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md:346-360`
- **Area:** compiler forwarding (`src/compiler/20.hir/hir_forward_decl.spl`,
  `src/app/desugar/forwarding.spl`)
- **Severity:** planning defect — T15 as scoped cannot be executed; no code
  regression

## What T15 asked for

> Wire `HirForwardDecl` into the simplest of `forwarding.spl`'s four phases
> (`fn name = target`) ... Acceptance: hop count strictly decreases and the
> text-generated body is absent for that phase.

The plan names two files plus an unnamed **"the HIR-lowering site"**
(`doc/03_plan/.../render_perf_replan_parallel_teams_2026-08-07.md:350-351`). A
prior agent flagged that this site is unnamed and the acceptance criterion is
weaker than its siblings' before passing over T15 in favor of T13.

## What was checked (evidence)

1. **`src/app/desugar/mod.spl` (the file that calls `desugar_forwarding`,
   `mod.spl:226`) is never called from `src/compiler/**`.**
   `grep -rln "app\.desugar\b" src/compiler/ src/app/cli src/app/build` — zero
   hits for `src/compiler`. The only reference from `src/app/cli` is
   `src/app/cli/_CliMain/main_and_help.spl:430-431`, which wires it to the
   standalone `simple desugar <file>` CLI subcommand
   (`src/app/cli/surface_alignment.spl:103`, `kind: "file_delegation"`) — a
   manual, opt-in, offline tool. It is not invoked by `build`, `test`, `run`,
   or the parser/HIR/MIR pipeline.

2. **Zero production `.spl` files use the syntax this pass targets.**
   - `alias fn X = Y` / `alias me X = Y` (Phase 2, the class-body form):
     `grep -rln '\balias fn \|\balias me ' src/ --include=*.spl` outside
     `src/app/desugar/**`, `_spec.spl`, and test dirs returns exactly one hit
     — `src/compiler/20.hir/hir_forward_decl.spl`, and that hit is a code
     **comment** documenting the syntax, not a use of it.
   - Bare module-level `fn name = target` (the "DEPRECATED" plain-symbol form
     T15 explicitly targets): `grep -rnE '^fn [a-zA-Z_][a-zA-Z0-9_]* =
     [a-zA-Z_]' src/ --include=*.spl` outside the desugar/spec dirs returns
     **zero** matches anywhere in the repo.
   - The parser has no native handling either: `grep -n "alias"
     src/compiler/10.frontend/core/parser.spl
     src/compiler/10.frontend/parser_types_expr.spl` — zero hits. `alias` is
     not compiler syntax; it exists only as text this offline desugar tool
     recognizes.

3. **The pass does what its own header says when invoked directly, confirming
   the mechanics but not the premise.** Running `desugar_forwarding` on a
   minimal fixture (`fn target(x: i64) -> i64: x + 1` / `fn alias_name =
   target`) through `bin/simple run` produces:
   ```
   # DEPRECATED: fn alias_name = target
   fn alias_name(x):
       target(x)
   ```
   i.e. one wrapper hop (`alias_name` → `target`) — the exact shape T15's
   acceptance criterion wants to shrink to zero hops via `HirForwardDecl`.
   That mechanic is real, but it never fires on any file this repository
   actually compiles.

## Conclusion

T15's premise — "`src/app/desugar/forwarding.spl` (504L text generator) is
still authoritative" for the plain-symbol phase — is **refuted for the live
compile path**. There is no "HIR-lowering site" to wire `HirForwardDecl` into
because:
- the text-generator pass that would need replacing is not part of
  compilation (only a manual CLI subcommand), and
- no source file anywhere in the tree exercises the syntax form in question,
  so there is no hop count in the live pipeline to strictly decrease.

Wiring `HirForwardDecl` into a real HIR-lowering pass for this syntax would
require first making the parser accept `alias fn`/bare `fn name = target` as
native grammar (currently it does not), then adding an HIR lowering arm for
it — which is new-feature work, not "wire an existing struct into an existing
pass" as T15 was scoped. That is out of bounds for a single bounded unit and
is not attempted here.

## What was landed

A characterization assertion recording today's real behavior of the *offline*
desugar tool (so the "hops don't exist in the live path" claim has a
regression tripwire, and so a future unit that DOES make `alias`/`fn name =
target` native grammar has a concrete before/after to compare against):
`test/01_unit/compiler/hir/hir_forward_decl_spec.spl` — new `it` asserting
`desugar_forwarding` on a plain-symbol fixture emits exactly the one-hop
wrapper body shown above. `HirForwardDecl` itself remains unwired into any
pass (unchanged from `56093d1d9d11`); `forwarding.spl` is untouched per T15's
"do NOT delete it" instruction.

## Next T-unit picked

None available. Per the launcher's unit list, T1-T20 minus {landed:
T3,T4,T5,T6,T8,T9,T10,T11,T13,T14} minus {forbidden collision: T1,T2 (held),
T12,T18,T19,T20 (other agents), T16,T17,T7 (Rust-seed edits forbidden)} leaves
only T15. This report is the full deliverable for this session.
