<!-- codex-design -->

# Release Process Hardening Agent Tasks

## Shared contract

Interfaces and manual/setup/checker names are frozen in `.spipe/release_process_hardening/state.md`. Unresolved scaffolds fail with `assert(false)` or `fail(...)`.

## Lanes

| Lane | Owner/output |
|---|---|
| Policy/version | Primary: requirements, policy schema, pure version/session checks |
| Beta/backport | Primary: typed backport admission and rejection tests |
| Candidate/promotion | Primary: immutable candidate, no-rebuild promotion, withdrawal checks |
| Spipe plugin/projections | Bounded sidecar inventory merged by primary; primary edits/version/parity acceptance |
| Tests/manual | Primary owns executable spec, docgen/manual review, and REQ traceability |
| Docs/wiki | Bounded sidecar inventory; primary performs `$spipe_doc_wiki_refactor` and final freshness review |
| Verification | Primary normal/highest-capability reviewer; sidecars cannot accept broad exclusions/done marks |

## Integration order

Policy contracts → pure implementation → focused tests → CLI → plugin/projections → docs/manual → verification. Preserve unrelated dirty files and do not combine other feature lanes.

## External handoff

Live ruleset deployment, signer configuration, promote-only GitHub workflow conversion, and real beta publication remain open until separately authorized. The handoff must name exact commands/receipts and may not claim release PASS.
