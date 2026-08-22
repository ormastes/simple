<!-- codex-design -->
# Agent Task Plan — Simple Compiler Performance and Memory Efficiency

## Authority

Merge owner and final highest-capability reviewer: `/root`. Generated-manual review owner: `/root`. Sidecars may implement bounded disjoint lanes but cannot change frozen interfaces, accept exclusions, or mark done.

## Dependency graph

```text
W0 baseline/ownership
 -> W1 vector containment + pass contracts
    -> W2 frontend/diagnostics || W3 MIR facts
       -> W4 typed first-release rules
          -> W5 CollectionPlan/COW || W6 pass rehabilitation
             -> W7 CostSummary/.sperf
                -> W8 .sprof-v2/curves/profile ranking
                   -> W9 tool hot paths
                      -> W10 docs/refactor/verify
```

## Frozen shared names

`PassStatus`, `PassExpectation`, `BackendDelegation`, `PassRunRecord`, `EffectivePipeline`, `PerfRuleId`, `PerfDiagnostic`, `OperationSummary`, `CostExpr`, `AnalysisIncomplete`, `PerfFacts`, `LoopFact`, `MemoryRegion`, `PerfSummary`, `CollectionPlan`, `CowUniqueness`.

Frozen manual steps/helpers are those in the system-test plan and `.spipe/.../state.md`. Unimplemented helpers fail explicitly.

## Waves and ownership

| Wave | Owner lanes | Gate |
|---|---|---|
| W0 | merge owner; read-only inventory sidecars | admitted binary, dirty-file ownership, one baseline/provenance ledger |
| W1 | vector containment owner; pass-contract owner; tests-only owner | unsafe rewrite excluded; effective pipeline truthful; sentinel/verifier works |
| W2 | frontend-session owner; diagnostic-contract owner; tests-only owner | one revision owner, exact spans, legacy COLL compatibility |
| W3 | disjoint CFG/dominance, loop/range, def-use/liveness, region/memory, escape/COW lanes; one facade/invalidation owner | one CFG build/revision; unknown fails closed |
| W4 | disjoint copy/COW, collection, materialization/capacity, layout/stack, invariant/allocation rule lanes; one registry owner | first-release positive/suppression/unknown matrix |
| W5 | operation/cost, plan extraction, lowering, COW evidence lanes | only pure proven plans transform; true preheaders and zero-trip safety |
| W6 | one mini-lane per pass in selected order | full activation/differential/idempotence/adversarial/perf gate per pass |
| W7 | summary/cache, remaining rule families, `.sperf`, CI tests | deterministic bounded SCC and confident-only regression policy |
| W8 | profile codec, instrumentation, curves, ranking | v1 compatibility; disabled no allocation/I/O; profiles never legality |
| W9 | lint/LSP/MCP/cache/tool hot-path owners | warm no scan/subprocess; startup/request/RSS evidence |
| W10 | docs/manual/refactor owner then independent verifier | all REQ/NFR evidence current; STATUS PASS required for release handoff |

Shared registries/exports are edited by their single owner only. Sidecars submit integration deltas rather than editing shared files concurrently. No lane introduces `40.collection_plan` or a `65` layer.

## Baseline and verification commands

Use the exact admitted native pure-Simple binary and record its hash/provenance. Baseline focused compiler/lint/optimizer/COW/tool performance before source edits. For every touched `.spl` file, run `bin/simple run src/app/optimize/main.spl <file> --full --level=O3` once after stabilization. Then run focused correctness and the identical performance command once.

Final scope includes `check src/compiler`, `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`, MCP stdio integration, owned-file lint/duplicate checks, direct env/process guards, optimizer integrity, requirement traceability, manual quality, and `find doc/06_spec -name '*_spec.spl' | wc -l` = 0.

## Risk gates

- No bulk pass activation.
- Unknown alias/effect/escape/range/cost rejects transformation.
- No raw runtime/env/process shortcut or Rust/C performance rewrite.
- No machine fix beyond ownership/lifetime/effect proof.
- No performance claim without same-binary provenance and repeated measurement.
- No profile-based semantic authorization.
- No implementation/done mark with fail-fast scaffold or missing manual.
- Maximum three fix/verify cycles per slice; stop and record remaining blocker.
## Active hardening tranche: SSA dominance receipts

- Merge owner: `/root`.
- Parallel review input: `ssa_verifier_design`, `verifier_integration_review`, and
  `architecture_perf_facts` lanes.
- Source owners: `mir_opt/perf_facts.spl` for bounded shared facts and
  `mir_opt/mod.spl` for optimizer-boundary policy.
- Acceptance: reject undefined, multiply-defined, use-before-def, non-dominating, and
  unavailable-dominance flows with stable codes; model call results on the normal edge.
- Performance gate: no verification work in normal builds, no dense liveness matrices in
  the verifier projection, and no definitions-by-uses Cartesian scans.
- Remaining follow-up: opcode typing, ownership, loop-boundary proof, exact module-pass
  outcomes, and admitted runtime differential evidence.

## Active hardening tranche: partial opcode typing

- Reuse the structural instruction traversal and one local-type index; do not add a
  second MIR walk or serialize type keys.
- Admit only exact local contracts for `Const`, `Copy`/`Move`, and `Cast`/`Bitcast`.
- Emit stable `MIRV025`-`MIRV027` codes and checked/unproved coverage counters at function
  and module level.
- Treat every other opcode as explicitly unproved until its full operand/result contract
  is designed and tested.
- Next type lanes: arithmetic/operator families, memory/pointer operations, aggregates,
  calls/signatures, SIMD/GPU, and terminators.

## Active tool tranche: allocation-free lint configuration membership

- Preserve the canonical `collection_performance` code mapping and evidence-tier policy.
- Replace per-entry `all_lint_names().contains` array construction/scanning in SDN and
  file attributes with allocation-free exhaustive membership.
- Pin enumeration/membership parity and reject the former source shape.
- Leave one-time enumeration consumers intact; do not introduce a mutable global cache or
  per-`LintConfig` registry dictionary.

## Active tool tranche: cached effective lint defaults

- Store the selected default-level table in `LintConfig` and refresh only on profile
  change.
- Share immutable defaults into child configs while copying only authored overrides.
- Require `get_level` to perform no registry construction, profile projection, source
  read, or allocation.
- Preserve collection evidence-tier warning caps and all allow/warn/deny behavior.
- Follow-up: cache project SDN parsing by path/revision and combine duplicate policy
  lookups only after output parity is pinned.

## Active tool tranche: request-local project policy reuse

- Bind file-parsed configuration to its exact `simple.sdn` source path.
- Skip reread/reparse when the base config already came from the discovered path.
- Retain only the immediately linted path/config for parsed AST rule append.
- Fail back to ordinary resolution on path mismatch; do not add a global cache without
  explicit revision invalidation and bounds.
- Follow-up: bounded directory-to-manifest cache keyed by canonical directory plus
  manifest size/mtime or digest for long-lived LSP/MCP sessions.

## Active tool tranche: one-pass diagnostic policy

- Introduce one evidence-aware suppression/severity decision record.
- Migrate central text/EasyFix filtering and parsed AST diagnostic append first.
- Preserve unknown-code, allow, warn, deny, typed-proven, and advisory-cap semantics.
- Pin absence of paired keep/level calls in migrated owners.
- Retain compatibility wrappers until query/LSP and remaining external callers migrate.

## Active tool tranche: shared request-local source view

- Add an explicit combined-lint entrypoint that retains the first line split.
- Reuse that COW view for parsed source-location indexing.
- Release on normal completion, non-Simple input, parse failure, and revision mismatch.
- Ensure ordinary/long-lived lint calls retain neither lines nor last-file policy.
- Follow-up: replace fallback location indexing with typed AST/HIR spans per producer.

## Active tool tranche: migrate line-view consumers

- Pass canonical lines into file-attribute policy resolution.
- Add compatibility `content` wrappers and allocation-free `*_lines` consumers.
- Migrate parameter-tag, raw-runtime fix, diagram, LLVM guard, name, freestanding, and WM
  owners without changing their order or predicates.
- Pin the normal call graph to line variants.
- Follow-up: extend the shared view through EasyFix registry owners and traceability rules.

## Completed tool tranche: quality-check line view

- Pass canonical lines to feature tracking, SPipe quality, and raw typed-UI checks.
- Remove five rule-local source splits without changing rule order or locations.
- Pin the normal call graph and forbid regression to content-taking method signatures.
- Follow-up: extend the shared view through EasyFix registry owners.

## Completed tool tranche: single EasyFix ownership

- Confirm `primitive_api` and `simple_script_required` are full-registry members.
- Remove their duplicate direct invocations and imports from normal lint.
- Pin registry membership and absence of duplicate call sites with source contracts.
- Follow-up: construct one bounded line/context view inside the registry.

## Completed tool tranche: shared SPipe EasyFix facts

- Add a canonical-lines registry entrypoint while retaining standalone compatibility.
- Build one request-owned `LineContext` array only for admitted spec files.
- Share contexts across four SPipe rules and lines with missing-docstring analysis.
- Pin normal lint dispatch and shared fact consumers with source contracts.
- Follow-up: migrate code/module/annotation EasyFix families into the same bounded view.

## Completed tool tranche: shared general EasyFix facts

- Construct one general request-owned context array from canonical lint lines.
- Migrate resource, struct, annotation, export/import-boundary, and SPipe consumers.
- Pass canonical lines to non-exhaustive-match and bypass analysis.
- Reuse lines/contexts in duplicate-typed-argument analysis, including per-signature calls.
- Preserve standalone compatibility wrappers and registry result order.
- Follow-up: index duplicate-typed call sites once and migrate remaining split-based rules.

## Completed tool tranche: compiler-owned EasyFix line migration

- Add canonical-line variants for star, wide-public, bare-bool, primitive, and script rules.
- Reuse shared contexts for short-grammar analysis.
- Add line-based file-scope allow handling for primitive APIs.
- Preserve allocation-free compatibility path gates on excluded files.
- Pin registry dispatch to every new view variant.
- Follow-up: migrate stdlib contextual-keyword/deprecation/stub scanners.

## Completed tool tranche: canonical EasyFix context owner

- Add stdlib `EasyFixSourceView` and a from-lines context builder.
- Add view entrypoints for contextual-keyword, deprecated-if-let, and stub rules.
- Re-export canonical stdlib context facts from compiler helpers; delete the duplicate type.
- Use one registry view for every compiler and stdlib context consumer.
- Pin single-view dispatch and absence of the compiler duplicate with source contracts.
- Follow-up: index duplicate-typed calls and audit remaining whole-source algorithms.

## Completed tool tranche: indexed duplicate-typed calls

- Count unique `(name, arity)` rewrite targets once and reject ambiguity fail-closed.
- Scan identifier/call sites once instead of once per signature.
- Store flat indexed replacements and restore signature/source order deterministically.
- Remove obsolete per-signature scan and uniqueness helpers.
- Pin indexed dictionaries and absence of the quadratic helper with source contracts.
- Follow-up: replace lexical candidates with typed resolved-call facts when available.

## Completed tool tranche: allocation-free annotation and EasyFix IDs

- Replace per-annotation whitelist arrays with exact allocation-free match dispatch.
- Decode namespaced and direct EasyFix ID formats through one helper.
- Fix W0404/W0406 policy identity so line numbers cannot become lint codes.
- Preserve malformed IDs as unknown authored codes rather than dropping diagnostics.
- Add functional ID-shape and source-allocation regression contracts.
- Follow-up: unify unknown decorator/attribute classification with typed annotation facts.

## Completed tool tranche: EasyFix policy reachability

- Compare emitted EasyFix semantic codes with configurable lint names/default levels.
- Add exact mappings for all already-declared EasyFix policy names.
- Map W0406 to the visibility-boundary family.
- Pin default-deny promotion and explicit-allow suppression behavior.
- Keep mapping allocation-free and shared by text/JSON policy projection.
- Follow-up: register intentional policy names for remaining advisory-only EasyFix codes.
