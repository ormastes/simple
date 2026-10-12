# Traceability, SDN, and Slop: domain re-research

<!-- codex-research: Astra, 2026-10-03 -->

This rechecks the external assumptions of the [full report](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md) against primary documentation. Local findings and proposed API ownership are in the [local companion](../local/simple_traceability_sdn_slop.md). Research date: 2026-10-03; local baseline: `88ecaa21054aea80eb7c8dd46052c344837fe78a`. Search retrieved primary-source excerpts; direct page fetching was not used. External documents motivate behavior and do not constitute Simple test evidence.

## Immutable Git subjects and ref protocols

Git documents pre-push rows containing local and remote refs and object identities, including the zero local identity for deletion. Therefore the adapter must capture and validate every row before child processes can consume input. New branches and deletions need explicit policy; they cannot be treated as normal old/new commit pairs. This supports REQ-TRC-008–010 and AC-TRC-010–016. [Git hook contract](https://git-scm.com/docs/githooks)

The cached diff-index mode is the index comparison interface, while cat-file provides batched object information/content. The latter frames content by byte length and explicitly represents missing objects; implementations must parse those boundaries rather than split arbitrary source content on newlines. Use NUL-safe path inventory and compatible batch framing with a tested minimum Git version. These are adapter recommendations inferred from the interfaces, not a claim that current Simple already uses them. [Git diff-index](https://git-scm.com/docs/git-diff-index), [Git cat-file](https://git-scm.com/docs/git-cat-file.html)

A source diff is a selector, not proof of the bytes eventually admitted. Bind staged checks to the selected index, push checks to immutable ref subjects, and merge admission to the actual candidate. Preserve sparse checkout independence and object-read failures as incomplete evaluation. Test the actual supported jj/SJ publication routes: this search did not establish a universal jj hook guarantee, and the report correctly refuses to infer one from Git-subprocess documentation alone.

## Trusted remote admission

GitHub documents that merge queues require the separate `merge_group` event; adding only PR/push handling cannot supply that check. Required-status troubleshooting also describes exact expected status producers. The actual landing branch's settings must be inspected separately from repository source and from the report's earlier settings observation. [Required-status troubleshooting](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks), [Actions events](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows)

GitHub's security guidance warns against executing untrusted PR content under privileged `pull_request_target` context. For this feature, the inferred control-plane design is a trusted checker, dependencies and policy whose subject is candidate data, with any candidate execution isolated and unprivileged. Pinning only a policy manifest while running a candidate-controlled gate script does not establish that separation. Test candidate no-op checker replacement and exclusion/baseline weakening with a real trusted adapter. [Secure pull_request_target usage](https://docs.github.com/en/actions/reference/security/securely-using-pull_request_target)

A no-relevant-change result should come from a running trusted classifier bound to the subject. Missing PR-only fields on push/merge-group must not produce a fabricated clean result. Report infrastructure failure, absent receipts and mismatched SHA as incomplete/non-green. These recommendations preserve REQ-TRC-011 and AC-TRC-017–020; they do not prescribe privileged execution as a shortcut.

## Incremental correctness

The original Build Systems à la Carte research provides a framework for comparing dependency handling and rebuild behavior. Its correctness discussion motivates comparison with recomputation over the final store. This supports independently testing incremental trace results against a full rebuild, rather than using the incremental engine as its own oracle. [Original publication](https://www.microsoft.com/en-us/research/publication/build-systems-la-carte/), [Research paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2018/03/build-systems.pdf)

Rust's compiler guide describes query dependencies, fingerprints, and red/green validation. A changed input can leave an output unchanged, but that can only be established through the dependency-aware computation. The guide also preserves query-read order because changed branching can change which dependencies matter. [Incremental compilation](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html)

For Simple, tracking missing-ID lookups, uniqueness queries, candidate-set membership, mapping policy, extractor and schema versions is a design inference. A change-only file cache misses creation of a previously absent target and addition of a second conventional candidate. Include deletes, moves, aliases, duplicate IDs, stale overrides and rule changes in randomized and directed equivalence fixtures. This retains all of REQ-TRC-017 and AC-TRC-005, 008, 009 and 028; cache hits and elapsed time alone are insufficient evidence.

## Requirement semantics and evidence

StrictDoc's guide describes explicit requirement/source traceability and labels its source-file traceability experimental. It is useful prior art for authored intent plus generated navigation, not a replacement for Simple's SDN, SSpec definitions, identities or runtime evidence. [StrictDoc traceability guide](https://strictdoc.readthedocs.io/en/stable/stable/docs/strictdoc_01_user_guide-TRACE.html)

The resulting Simple design keeps definition links separate from execution observations and evidence eligibility. Directory convention is structural association; requirement text found in examples is not a semantic claim. Executed acceptance scenarios do not imply that linked unit/integration/component tests ran. These are report contracts to prove with production-path tests, not claims established by external products.

Retain separate outcome, validity, applicability and qualification records. Evidence provenance must bind observed artifacts to definition/source/config/expectation/binary/lane identities; a correctly shaped hash does not establish those facts. The single existing runner/database owner should finalize immutable run records, including failures and interruption where recoverable. No external structured interchange format is adopted: all Simple-owned records remain SDN.

## Layered views, accessibility and safe export

ELK Layered documents directional layers, routing modes, ports and compound graphs with cross-hierarchy edges. Use these as layout behavior references: stable semantic columns, component grouping and explicit back-edges are appropriate. ELK's separate JSON format is not selected; neither its runtime nor any foreign graph protocol is required. Layout limits affect visible projection only, never evidence qualification. [ELK Layered](https://eclipse.dev/elk/reference/algorithms/org-eclipse-elk-layered.html)

The W3C tree-view pattern distinguishes focus from selection and defines arrows, Home/End, activation and type-ahead behavior. Slop acceptance must drive keyboard interaction and verify preserved focus after refresh, not merely inspect a tree data structure or ARIA labels. Provide a readable relationship-list alternative to the graph. [W3C tree-view pattern](https://www.w3.org/WAI/ARIA/apg/patterns/treeview/)

OWASP describes context-specific output encoding and warns that quote escaping alone is insufficient. Static HTML should render source/Markdown as data, validate link schemes and visibility, and avoid inserting untrusted content into executable contexts. Test hostile source, attributes and URLs in an actual exported page. This reinforces AC-TRC-032 and 040; it does not authorize importing a new sanitizer dependency without local API review. [OWASP XSS prevention](https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html)

Revision-pinned source, lost-delta resynchronization, last-valid display and canonical node identity across tree branches are Simple-specific contracts. External UI patterns cannot prove them. They require AC-TRC-033–037 production integration evidence, including current/last-valid distinction and hidden-count visibility.

## Remaining decisions and evidence obligations

The complete report scope is retained. Primary research supports its separation of intent, derived graph, observations and trusted admission. Local source adds a concrete implementation constraint: shared canonical SDN encoding does not guarantee nested table round trips. Freeze a supported schema representation and prove reject/round-trip cases before parallel implementation depends on it.

The user's instruction to implement the saved report selects its full requirements and NFR targets, as confirmed by parent coordination. Timing targets remain unmeasured. Required follow-through includes an admitted source-matched binary, real exact-snapshot and publication adapters, full 40-case acceptance coverage, modern SSpec manuals generated from actual execution, and feature self-traceability. Neither these documents nor historical reports satisfy those gates.
