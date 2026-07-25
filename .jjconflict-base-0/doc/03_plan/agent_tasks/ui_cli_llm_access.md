<!-- codex-design -->
# UI CLI LLM Access — Agent Task Plan

## Shared contract fixed before implementation

- Types: `AccessCommandDescriptor`, `AccessOperation`, `AccessRequest`, `AccessResult`, `AccessError`, `AccessSafety`, `AccessOutputMode`.
- Existing payloads: `UiAccessSnapshot`, `WinTextSnapshot`; no parallel model.
- Manual steps: `Start UI access`, `List active windows`, `Inspect TUI rendering`, `Inspect GUI rendering`, `Find an interactive target`, `Act on the target`, `Review access history`.
- Setup/checker: `setup_ui_cli_access`, `check-ui-cli-access` implemented as `scripts/check/check-ui-cli-access.spl`.
- Any temporary helper must call `fail(...)` or `assert(false)`; no fabricated marker/output may pass.

## Lanes

| Lane | Scope | Owned paths | Current assignment | Depends on |
|---|---|---|---|---|
| A — common grammar | Shared records/parser/validation/rendering and WinText layering fix | `src/lib/common/ui/access_cli_grammar.spl`, `access.spl`, `win_text_access.spl`, focused unit specs | `N/A` — frozen before this continuation; primary merge owner | selected design |
| B — T32 adapter | Descriptor/result/error/output mapping with T32-only compatibility | `examples/10_tooling/trace32_tools/t32_cli/**`, related `t32_mcp/**`, `test/01_unit/app/t32_cli/access_cli_grammar_spec.spl` | `spark_t32_completion`; primary merge owner reviews | Lane A |
| C — UI adapter | Existing test-API client, read-only DB fallback, deployed CLI routing | `src/app/ui/{access_cli,cli_entry}.spl`, `src/app/ui.test_api/handler.spl`, `src/app/cli/_CliMain/main_and_help.spl`, `src/app/cli/cli_helpers.spl`, `test/fixtures/ui_cli_access/live_server.spl`, focused UI tests | `spark_ui_wm_completion` for common projection/focus; primary merge owner for routing/revision | Lane A |
| D — WM adapter | Live list/conversion/action and play dispatch | `src/app/play/{main,wm_access_cli}.spl`, `src/lib/nogc_sync_mut/play/wm/mod.spl`, `test/01_unit/app/play/wm_access_cli_spec.spl` | `spark_ui_wm_completion` audit; primary merge owner for generation safety | Lane A |
| E — evidence/docs | Pure-Simple checker, SSpec/manual, captures, guide freshness, perf evidence | `scripts/check/check-ui-cli-*.{spl,shs}`, `test/03_system/app/ui_cli_llm_access/**`, `doc/06_spec/03_system/app/ui_cli_llm_access/**`, `doc/07_guide/app/ui/{ui_access,ui_cli_llm_access}.md`, this plan | Peirce (`spark_manual_docgen`), Maxwell (`spark_t32_artifact_recovery`), and `spark_evidence_completion`; primary merge owner accepts all output | A-D merged |

Independent implementation work may run in parallel only after Lane A signatures compile. T32/UI/WM lanes must not edit common signatures independently.

## Ownership and review

- Merge owner: primary Codex agent in the default `ui-cli-llm-access` lane.
- Historical sidecars Peirce and Maxwell owned manual/docgen and T32 artifact
  recovery. This continuation used `spark_t32_completion`,
  `spark_ui_wm_completion`, and `spark_evidence_completion`; the primary merge
  owner reviewed and integrated their bounded outputs.
- Generated-manual owner: evidence/docs lane drafts; merge owner reads it as an operator manual and repairs steps/captures.
- Final static reviewer: `higher_merged_review`, after the primary merge
  owner has converged all lanes. The reviewer must accept architecture, dependency
  direction, shared T32 grammar, live transport, action safety, implementation,
  focused evidence, performance evidence, generated-manual quality, exclusions,
  and done status, then bind that acceptance to the clean full revision and
  canonical evidence-manifest digest. No receipt is written before that review.

## Merge order

1. A common grammar and unit checks.
2. B/C/D adapters rebased on the frozen common contract.
3. Merge owner resolves only interface mismatches; no duplicated compatibility implementation.
4. E checker, system spec/manual, guide, and perf evidence.
5. Refactor/doc freshness pass.
6. One converged verification and highest-capability completion audit.

## Stop rules

- Maximum three verify/fix cycles.
- Never rerun an already-green acceptance check in this session.
- Missing live adapter/capture/perf evidence remains FAIL; no planned or source-string marker substitutes.
- Unrelated dirty files and other active lanes are preserved and excluded from commits.
