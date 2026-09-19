# compiler Layer Expert

## Role

Maintain process knowledge for the `compiler` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/compiler` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/compiler/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)
- [Collection planner: adaptive collections + typed queries (RC1 plan)](../../03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md)
- [mold-MDSOC++ linker (RC1 plan)](../../03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md)

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

- 2026-09-08 enum-pattern aliases: `interpreter_patterns.rs` resolves a
  qualified pattern's imported `EnumType` alias before comparing the runtime
  enum identity. Preserve the positive explicit-alias case and the negative
  conflicting-glob control in the focused Rust regression.

- 2026-09-05 gpu_frontend_offload: default-off frontend offload switch (`structural_contracts/frontend_offload_switch.spl`, driver gate in `80.driver/driver_source_pipeline_parsing.spl`) — see `doc/00_llm_process/feature_expert/gpu_frontend_offload/skill.md`.

## Traps (arena AST / lint rules) — measured 2026-09-19

Found while fixing the COLL0xx rule family
(`doc/08_tracking/bug/coll020_lint_fix_disagree_two_array_dedup_2026-09-19.md`).
All three cost real time and none is guessable from the source.

- **`span_is_valid(0)` is TRUE, and span id 0 is a lie.** `span_is_valid`
  (`10.frontend/core/types.spl`) is just `id >= 0 and id < pool.len()`, and id
  0 is a genuine pool slot holding whatever the first allocation of the run
  recorded. The parser also passes 0 as its "no span" default, so reading a
  0 span hands you a position from an unrelated part of the file (measured:
  every unspanned node reported line 2, col 23 for one fixture). **Gate on
  `span_id > 0`, not on `span_is_valid`.** Relatedly, only SOME node kinds
  carry spans at all: EXPR_METHOD_CALL, EXPR_SLICE and STMT_IF do;
  EXPR_IDENT and most statement tags do not. Anchor a diagnostic on a node
  that does.
- **String interpolation is opaque, and NOT as `EXPR_INTERPOLATED_STRING`.**
  `val t = "{x.len()}"` parses to a plain **`EXPR_STRING_LIT`** whose text is
  the literal `{x.len()}`, with ZERO child expressions — the hole is raw text
  and is lowered later. Checking for tag `EXPR_INTERPOLATED_STRING` finds
  nothing. Any "is this identifier used anywhere?" analysis is blind to uses
  inside `"{...}"`, which is safe for a rule that must find a use and UNSAFE
  for a rule that must prove there is none. Also: a spec fixture containing a
  literal `{` is interpolated in the SPEC's own scope before the linter ever
  sees it — build such fixtures by concatenation (`"{" + "x" + "}"`).
- **Walk `expr_child_exprs`, never a hand-rolled tag switch.**
  `10.frontend/core/_AstExpr/accessors.spl` has the arena's canonical,
  tag-dispatched ownership contract; it deliberately excludes slots that hold
  match-arm ids or field-name metadata rather than expression ids, so it can
  neither miss a child nor misread a non-expression slot. The hand-written
  switch it replaced in `collection_patterns.spl` silently missed
  EXPR_SLICE, literals, and call receivers.
- **A `lazy` import loads on CALL, so a perf gate must sit at the call site.**
  Moving a `source.contains(".contains(")` gate from the caller into the lazy
  callee made every COLL-free file pay the lint/parser frontend load: 2.68s ->
  4.03s on a two-line file. The gate belongs outside the lazy call.
