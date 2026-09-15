# DevHub multi-target gateway agent tasks

- Item 1: named targets/selectors/default/persistence — `confluence_map`.
- Item 2: ordered multi-value header validation — `devhub_map`.
- Item 3: gateway-aware Confluence transport — Astra.
- Item 4: N/A; no item 4 was supplied.
- Item 5: automatic target/classification headers — `devhub_map`.
- Item 6: deployment mismatch warning/silence — `confluence_map`.
- Item 7: diagnostic secret redaction — `devhub_map`.
- Cross-provider gateway/nested-header completion, including normal Jira
  `JiraClient` transport and Bitbucket Data Center build-status routing —
  implementation lane in the shared worktree; final acceptance remains with
  the merge owner.
- Documentation and REQ/source/test trace audit — `docs_trace_audit`, with
  transport-contract alignment by `docs_transport_update`.
- Merge owner: root Codex. Final reviewer: Astra.

Implementation and documentation are present. Runtime execution, manual
regeneration, command-dispatch gap closure, and final reviewer acceptance remain
open; no docs-only progress mark implies `STATUS: PASS`.

Progress and remaining merge gates are tracked in
`doc/03_plan/app/tools/devhub_multi_target_gateway_plan.md`.
