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
| Scoped self-review | Primary: external deny/constraint DB, pure evaluator, exact changed-path manifest, GitHub Actions check broker, ruleset projection, bootstrap plan |
| Spipe plugin/projections | Bounded sidecar inventory merged by primary; primary edits/version/parity acceptance |
| Tests/manual | Primary owns executable spec, docgen/manual review, and REQ traceability |
| Docs/wiki | Bounded sidecar inventory; primary performs `$spipe_doc_wiki_refactor` and final freshness review |
| Verification | Primary normal/highest-capability reviewer; sidecars cannot accept broad exclusions/done marks |

## Integration order

Policy contracts → pure implementation → focused tests → CLI → plugin/projections → docs/manual → verification. Preserve unrelated dirty files and do not combine other feature lanes.

## External handoff

Promote-only workflow conversion and the live ruleset/environment baseline are
implemented. Compiler PRs #29 and #31 and release-process PR #28 are integrated
on `main`; they are no longer open prerequisites. The candidate workflow source
repair still needs default-branch provider proof because the prior file produced
path-named zero-job push failures. Independent candidate-review broker approval,
signer use, creation of the real maintenance line, fresh Stage 3/4 plus whole-
suite evidence, and real beta candidate/publication receipts remain open. The
handoff must name exact commands/receipts and may not claim release PASS.

Candidate qualification must build the sole receipt-free Stage 2 trust root,
produce and consume typed planner receipts for Stage 3 and Stage 4, and pass
runtime-backed version/support plus reviewed convergence checks before recording
the create-once reservation. The periodic fresh-runner checkpoint is a bounded
Git-only source observation and is never an admission receipt.
