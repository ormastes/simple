# B3 semantic Markdown lint/fixer

REQ-MC-008, original accepted plan section 5.4. Status CODED / UNRUN; higher-model source review and root CLI registration pending. Existing common Markdown helpers have no link destination byte spans; llm_process_gen only scans naive inline links. New scanner owns bounded destination spans rather than pretending either provides semantic authority.

`SemanticMarkdownSourceV1(local_file, remote_file, document)` configures exact local/GitHub blob destination authority using B2's existing parsed snapshot. No inferred package/module, remote fetch, current Git revision, signature schema, or outline parser. Remote destination matches the entire configured blob URL including revision. Unknown/duplicate mappings remain diagnostics with no fix.

`plan_semantic_markdown_links_v1(markdown, bindings, critical)` returns SHA256-bound `SemanticMarkdownPlanV1(revision, diagnostics, sources)`. Each diagnostic has W-DOC-AST-001, warn or deny, original byte range/target, replacement or refusal message. Handles inline destinations, reference-definition destinations, angle destinations, bare src/... locations and GitHub URLs; local .spl#Lx[-Ly] and .spl:x[-y] forms. Scanner protects matching fenced code/backtick spans, indentation code, escaped source examples, link labels, quoted link titles and HTML comments. This is a bounded source-location scanner, not a new complete Markdown renderer. Complex unsupported destination syntax remains without a guessed edit. Existing spl: links are not line-location targets. No reviewed transient-report exception registry exists in the inspected owners, so there is no bypass.

`apply_semantic_markdown_links_v1(markdown, plan)` replans against exact source snapshots, checks the full Markdown SHA256 and every proposed target/replacement against fresh production resolver output, validates ordered disjoint edits, checks source revisions at publication and returns all replacement bytes or an error. It writes nothing. A stale, unresolved, ambiguous or forged plan publishes no partial output.

Bounds: 1MiB Markdown/source, 4096 targets/bindings/declarations. Scanner has an 8*input+64 probe limit for pathological unmatched inline spans. B2 additive `semantic_links_from_lines_v1(document,revision,ranges,package_qualified)` indexes line bounds once and reconstructs actual parsed source authority exactly once per source/form group and performs at most four bounded source reads per group, never per link. Range/declaration ranking is bounded at 4096² comparisons. The plan holds copied diagnostics and caller snapshots; disposal/replacement is explicit invalidation. No workspace walk, global cache, process or env read. One charged serial producer parse per nonempty source/form batch authenticates externally mutable snapshots. Apply reuses the grouping path and performs final source checks. Runtime/RSS/latency/coverage UNRUN.

CLI adapter `app.cli.doc_links.doc_links_command_v1(args)` excludes leading `doc` and accepts:

```
doc check-links --markdown FILE --source-file SOURCE --source-link src/X.spl --package P --module M --revision SHA256 [--remote-link EXACT_GITHUB_BLOB_URL] [--critical]
doc fix-links --markdown FILE --source-file SOURCE --source-link src/X.spl --package P --module M --revision SHA256 [--remote-link EXACT_GITHUB_BLOB_URL] [--critical]
```

Check output is diagnostic text; warn exit0, critical with diagnostics exit1. Fix output is complete Markdown bytes for stdout, with no in-place write; refusal is Err. Root owns shared CLI route and presentation. Single source mapping at CLI, multiple explicit bindings at library. llm_process_gen should_check_link excludes spl: from filesystem existence checks.

Five real-file scenarios cover mixed local/colon/GitHub reference links, code/label/escape protection, critical severity, unknown mappings, stale Markdown/source, remote revision mismatch, both CLI operations. Source-only whitespace check PASS once before final docs. Runtime/docgen/sspec-maintain/core smoke UNRUN per parent phase-path constraint. Full B3 production acceptance and full B2 node-kind coverage are not claimed.


Revision2: public snapshot cache facts are untrusted. Replanning applies the repaired B2 actual-source batch producer, so forged declarations/indexes/spans cannot certify invented replacements. A new scenario directly constructs an altered public plan replacement and requires refusal. Source/file/package/module/revision are explicit configured producer inputs; no automatic authority discovery. All runtime checks remain UNRUN.


## Revision3 existing semantic destinations and process-doc caller

The shared Markdown destination scanner now recognizes existing `spl:` URI destinations before fragment removal, preserving code/label/title/comment protection. Actual `spl:` destinations are syntax-checked by the existing common URI parser, assigned to a unique explicit package/module source owner, then validated in a repaired actual-source resolver batch per owner. Valid destinations remain unchanged with no diagnostic. Missing owner, malformed URI, dangling name, stale fingerprint, wrong authority or stale source returns the existing `SemanticLinkErrorV1` with destination/byte context. No additional diagnostic ID is introduced. All check/fix callers propagate the error; semantic failures never become a success with zero findings. Existing W-DOC-AST-001 remains solely the selected line-location policy.

`semantic_markdown_process_failures_v1(markdown, bindings)` converts those typed shared errors into process-check failure text. The actual existing process generator caller is now public `check_process_document_links_v1(root,path,fallback_base)`, used by its existing check/generate call sites. It invokes the shared scanner/resolver before its legacy local-link fragment stripping. This generator has no source package/module/revision owner, so it passes empty bindings and intentionally fails closed on semantic destinations with a required-owner message. It cannot validate legitimate semantic links positively until an explicit caller owner is configured. The configured `doc check-links` / `doc fix-links` adapter already provides that owner and tests cover legitimate positive and malformed negative counterparts.

Additional real-file scenarios cover existing short semantic inline/reference destinations unchanged, malformed/dangling/stale fingerprints and changed source refusal, configured doc check/fix success/refusal, and the actual process-doc checker missing-owner refusal plus protected code examples. Source-only third review cycle; all runtime/docgen/NFR execution remains UNRUN. No per-link parse/read: existing semantic URI grouping uses one repaired source-producer parse per owner batch. Mixed location and semantic groups may require separate charged batches, each bounded at4096 items and1MiB source.

## C4 corrections (source candidate; all execution UNRUN)

The existing process generator validates the rendered candidate body through
`check_process_document_content_links_v1` before dry-run success or publication,
including forced overwrite. The file-check API delegates to that content owner;
non-Markdown behavior stays unchanged. Semantic source configuration is still
absent for the process generator, so actual semantic destinations refuse rather
than acquire guessed authority. Ordinary generated Markdown remains supported.

`resolve_semantic_links_source_indexed_v1` preserves one actual producer parse
per bounded batch and reports the exact failing URI input row. Whole-source
admission/revision failures use row -1. The Markdown wrapper maps a URI row to
its original target byte interval; it never blames the first valid destination
for a later failure or invents a location for a global admission error.
