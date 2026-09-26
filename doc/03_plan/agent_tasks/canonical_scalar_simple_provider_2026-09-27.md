# Canonical Simple scalar provider — implementation handoff

**Status:** design handoff; no provider admitted. **Merge owner:** root Codex. **Final reviewer:** independent normal/highest-capability review of semantics, manual quality and source-matched evidence. **Sidecar lanes:** N/A for this design-only change; later implementation may split only after the interface and fixtures below are frozen.

## Frozen interface and evidence names

- Common value types: `ParseGrammarProgramV1`, `ParseActionProgramV1`, `ParseDialectProgramV1`.
- Scalar executor: `parse_run_canonical_scalar_v1(dialect, request)`.
- Compiler adapter: `simple_dialect_program_v1`, `simple_canonical_ast_bridge_v1`.
- Comparator: `ParserSemanticSnapshotV1`, with `parser_semantic_snapshot_v1` and `expect_parser_semantics_equal` test helpers.
- Setup/checker helpers: `setup_isolated_frontend_sessions`, `setup_canonical_simple_fixture`, `expect_legacy_oracle_independent`, `expect_candidate_admission_receipt`, `expect_parser_resource_budget`.
- Manual `step("...")` names: `Build the canonical Simple grammar and action program`; `Parse the same Simple fixture in isolated legacy and canonical sessions`; `Compare complete semantic snapshots and diagnostic order`; `Refuse incomplete dialect and stale generation`; `Admit the scalar provider with parity and resource evidence`; `Reject SIMD promotion without scalar evidence`.
- Until backed by real execution, each new executable helper must use `fail("NOT IMPLEMENTED: ...")` or `assert(false)`. Existing EODL REQ-008/009 helpers stay fail-fast.

## Ordered implementation tasks

| Order | Owner surface | Deliverable and gate |
|---|---|---|
| 1 | Compiler frontend inventory | Pin independent oracle revision/schema; enumerate every Simple rule, action, transform, recovery and diagnostic branch against retained fixtures. |
| 2 | `std.common.structural.parse` | Implement bounded typed grammar/action records and validators; reject malformed version, opcode, offsets, counts and nonprogress cycles before execution. |
| 3 | `std.nogc_async_mut.structural.parse` | Interpret scalar grammar/actions against snapshot-owned tokens; count, reserve and emit source-ordered output without legacy parser calls. |
| 4 | Compiler structural adapter | Derive the Simple program from the inventoried existing grammar and bridge generic events to the existing AST/HIR representation. |
| 5 | Test and benchmark owner | Run isolated semantic differential corpus and pinned latency/RSS/allocation comparison; update executable specs, generated manuals and receipts. |
| 6 | Frontend admission owner | Admit only a complete candidate and pin grammar/action/schema/source generations; retain independent legacy oracle and fail closed on stale or partial evidence. |

Do not merge a source-only provider or count lexical parity as semantic parity. The reviewer checks no candidate call chain reaches handwritten rule/action bodies, that the legacy oracle stays independently executable, and that the generated manual states the observed result rather than planned behavior. The design authority is `doc/05_design/compiler/canonical_scalar_simple_grammar_action_provider_2026-09-27.md`.
