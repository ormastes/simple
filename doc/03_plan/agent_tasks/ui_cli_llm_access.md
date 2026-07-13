<!-- codex-design -->
# UI CLI LLM Access — Agent Task Plan

## Shared contract fixed before implementation

- Types: `AccessCommandDescriptor`, `AccessOperation`, `AccessRequest`, `AccessResult`, `AccessError`, `AccessSafety`, `AccessOutputMode`.
- Existing payloads: `UiAccessSnapshot`, `WinTextSnapshot`; no parallel model.
- Manual steps: `Start UI access`, `List active windows`, `Inspect TUI rendering`, `Inspect GUI rendering`, `Find an interactive target`, `Act on the target`, `Review access history`.
- Setup/checker: `setup_ui_cli_access`, `check-ui-cli-access` implemented as `scripts/check/check-ui-cli-access.spl`.
- Any temporary helper must call `fail(...)` or `assert(false)`; no fabricated marker/output may pass.

## Lanes

| Lane | Scope | Owned paths | Depends on |
|---|---|---|---|
| A — common grammar | Shared records/parser/validation/rendering and WinText layering fix | `src/lib/common/ui/access_cli_grammar.spl`, `access.spl`, `win_text_access.spl`, focused unit specs | selected design |
| B — T32 adapter | Descriptor/result/error/output mapping with T32-only compatibility | `examples/10_tooling/trace32_tools/t32_cli/**`, T32 parity tests | Lane A |
| C — UI adapter | Existing test-API client, read-only DB fallback, deployed CLI routing | `src/app/ui/access_cli.spl`, `cli_entry.spl`, focused UI tests | Lane A |
| D — WM adapter | Live list/conversion/action and play dispatch | `src/app/play/wm_access_cli.spl`, `main.spl`, focused WM tests | Lane A |
| E — evidence/docs | Pure Simple checker, SSpec/manual, captures, guide freshness, perf evidence | checker/system/perf/doc paths on feature slug | A-D merged |

Independent implementation work may run in parallel only after Lane A signatures compile. T32/UI/WM lanes must not edit common signatures independently.

## Ownership and review

- Merge owner: primary Codex agent in the default `ui-cli-llm-access` lane.
- Sidecars: design used independent architecture, UI/guide, and SSpec/test-plan lanes. Implementation may use A-D sidecars with disjoint files after common signatures freeze.
- Generated-manual owner: evidence/docs lane drafts; merge owner reads it as an operator manual and repairs steps/captures.
- Final reviewer: primary highest-capability Codex model after all merges. It must accept architecture, dependency direction, shared T32 grammar, live transport, action safety, implementation, focused evidence, performance evidence, generated-manual quality, exclusions, and done status, then bind that acceptance to the clean full revision and canonical evidence-manifest digest.

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
