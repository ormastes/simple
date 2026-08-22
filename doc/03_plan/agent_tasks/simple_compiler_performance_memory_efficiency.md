<!-- codex-design -->
# Agent Task Plan — Simple Compiler Performance and Memory Efficiency

## Diagnostic JSON serialization follow-up

- Merge owner: compiler performance/memory lane.
- Review evidence: parallel warning-policy audit identified duplicated five-pass
  whole-message escaping in both active query serializers.
- Implementation: place the exact one-pass escaper in `query_rich_common` and
  delegate both lint and compiler-diagnostic paths to it.
- Compatibility: retain the five legacy escapes, Unicode, JSON envelopes,
  diagnostic order and severity behavior.
- Performance acceptance: unchanged messages allocate no replacement buffers;
  escaped messages use one scan plus one final join rather than five full-text
  replacements.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and ownership review only.

## Workspace diagnostic session follow-up

- Add `compiler/90.tools/workspace_diagnostics` config/request/result/session
  owners; keep the first implementation serial and Pure Simple.
- Replace per-file `_run_simple_check` and nested JSON query subprocesses with a
  fresh per-file compiler/lint request inside one session.
- Preserve discovery and diagnostic order, clean-file JSON omission, summaries,
  exit codes and failure isolation; reset every mutable compiler/lint owner.
- Require zero per-file subprocesses and standalone/session parity fixtures before
  enabling the LSP path.
- Instance-own parser/lexer/AST state and add contamination stress coverage before
  any bounded parallel execution.
- Measure the same 50/200-file fixtures: cold/warm p50/p95, process count and max
  RSS; targets are >=50%/75% wall reduction and <=10% peak-RSS increase.

## Variable-reassignment dictionary tranche

- Replace analyzer-local count/alias parallel arrays and borrowed/escaped arrays
  with scalar dictionaries; retain shared legacy count helpers used by SSA lowering.
- Preserve raw scan order, exact-destination counts, old-root borrow/escape capture,
  alias resets, the 64-hop guard, local ID 0 and reason precedence.
- Remove unused non-alias escape collectors so they cannot be mistaken for the
  active, broader escape model.
- Pin copied-alias borrow followed by alias overwrite in both mirrored specs.
- Pin 256 distinct locals, exact reassignment total, safe flags and exact JIT fact
  ordering; do not derive output ordering from dictionary iteration.
- Performance acceptance: expected `O(I*64 + L)` lookup work and `O(L)` retained
  scalar state, with no growing parallel-array map/set in the active analyzer.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel semantic review only.

## Bare-import rewriter assembly tranche

- Replace the changed-file prefix concatenation loop with `new_lines.join("\n")`.
- Preserve split-derived blank lines, trailing-newline shape, matched-line output,
  atomic persistence and `-1/0/1` status behavior.
- Remove the now-unused text import and pin the shared-join/absence-of-prefix-loop
  contract in the existing atomic-rewriter spec.
- Performance acceptance: changed-file reconstruction copies `O(S)` output bytes,
  not `O(S*L)` cumulative prefixes; retained line storage remains unchanged.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel review only.

## Shared short-grammar identifier rewrite tranche

- Add canonical contains/plain/interpolation helpers to the cycle-free EasyFix
  rules-helper owner and both stdlib facades.
- Replace four compiler/stdlib immutable character-concatenation loops with thin
  delegates; remove discarded-output contains probes.
- Preserve ASCII whole-token boundaries, context-blind plain matching, Unicode,
  legacy boolean interpolation state, doubled braces, malformed braces, sequential
  tuple rewriting and the `_` no-change probe.
- Pin boundaries, Unicode adjacency, empty parameter, escaped/triple braces and
  all four delegation paths in mirrored short-grammar specs.
- Performance acceptance: unchanged input allocates no output; changed input uses
  match-proportional fragments and one join, with no growing result concatenation.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel semantic review only.

## MCP diagnostic wrapper assembly tranche

- Move wrapper JSON construction into cycle-free `query_rich_common`.
- Cache count text, append envelope/diagnostic/comma fragments and join once.
- Delegate active `query_diagnostics` and legacy `query_check` entrypoints to the
  shared emitter; preserve their public command behavior.
- Pin exact empty and multiple/nested-diagnostic output plus order and both caller
  delegations in mirrored query diagnostic specs.
- Performance acceptance: no full `diags_array` or structured-content
  intermediate; `O(S + D)` work, `O(D)` fragments and one final output allocation.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel review only.

## ANSI-free query diagnostic follow-up

- Merge owner: compiler performance/memory lane.
- Add an ESC-presence fast path to `_strip_ansi`; return the original compiler
  output when ANSI stripping cannot change it.
- Preserve exact legacy ANSI/malformed-sequence behavior on the slow path.
- Pin plain Unicode, multiple terminated sequences and unterminated sequences in
  mirrored query-diagnostic contracts.
- Record repeated normalization and workspace process-per-file work as
  architecture follow-ups rather than changing query APIs in this bounded tranche.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and ownership review only.
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

## Completed tool tranche: advisory EasyFix policy completeness

- Register contextual, deprecated, struct, grammar, raw-unit, and SIMD policy names.
- Add warning defaults and allocation-free known-name membership.
- Map four short-grammar wire codes to one stable policy family.
- Pin direct/family mappings and authored allow suppression behavior.
- Follow-up: generate code/name/default parity from one machine-readable descriptor.

## Completed tool tranche: honest unknown-annotation fallback

- Add one union-based source fallback with one diagnostic per unknown annotation.
- Replace dual decorator/attribute registry scans with the generic owner.
- Register `unknown_annotation` and alias legacy policy names bidirectionally.
- Preserve legacy standalone rule entrypoints for compatibility.
- Pin known decorator/attribute suppression and unknown single-result behavior.
- Follow-up: move category-specific classification to typed HIR.

## Completed compiler tranche: remove unsafe hoist bodies

- Confirm both collection-hoist entrypoints are fail-closed identities.
- Delete unreachable header-insertion implementations and private-only helpers.
- Retain independently useful scalar/invariance analysis predicates without transforms.
- Pin absence of dormant rewrite markers/header insertion with source contracts.
- Keep real preheader/effect/alias/speculatability requirements explicit.
- Follow-up: implement LICM only on shared canonical loop and memory facts.
## Completed compiler tranche: remove dormant trip-count recognizer

- Keep loop trip counts unknown until SCEV-lite supplies the complete proof contract.
- Delete the unreachable comparison-bound recognizer and its private-only helpers.
- Pin the absence of dormant recognizer markers and helper names with a source contract.
- Preserve natural-loop discovery and complete `(from,to)` exit-edge facts.
- Follow-up: implement bounded SCEV-lite as a shared immutable analysis with explicit invalidation.
## Completed compiler tranche: remove unsafe dormant TCO

- Preserve the `Skeleton` descriptor, factory, statistics, and identity compatibility entrypoints.
- Delete the unreachable sequential parameter-assignment rewrite and private candidate helpers.
- Pin absence of the unsafe rewrite surface with a source contract.
- Require parallel temporaries and full arity/type/ownership/effect/unwind/debug proofs before rehabilitation.
- Follow-up: implement the active transform only after shared call-edge and ownership facts exist.

## Planned tooling tranche: CLI-scoped lint session

- Construct the lint descriptor registry once per repository command.
- Cache manifest discovery and parsed policy per unique project configuration.
- Load critical-mode policy once per command.
- Read each source once and share it with optional SIMD analysis.
- Keep `run_lint_file` as a one-file compatibility wrapper.
- Pin diagnostic ordering/policy equivalence and measure batch wall time plus maximum RSS.
## Completed tooling tranche: command-scoped lint registry reuse

- Add `run_lint_file_with_linter` and retain the standalone compatibility wrapper.
- Construct one `Linter` outside the repository file loop.
- Reuse the most recent parsed project policy through a command-owned bounded cache.
- Clone cached policy before file/CLI overrides to prevent cross-file mutation.
- Pin registry construction and cache ownership with source contracts.
- Follow-up: cache manifest discovery and critical policy, then share one source read with SIMD/fix paths.
## Completed tooling tranche: one lint/SIMD source read

- Add a source-owned command entrypoint while retaining file-reading compatibility wrappers.
- Read each repository source once through the tagged lint reader.
- Share the exact payload with ordinary lint and optional SIMD analysis.
- Preserve valid-empty-file versus read-error behavior.
- Keep fix application on a fresh validated disk read before mutation.
- Follow-up: cache directory-to-manifest and critical-mode policy resolution.
## Completed tooling tranche: critical policy session snapshot

- Resolve `critical.dynamic_acquire` lazily on first linted file.
- Retain only the effective scalar mode in the command-owned `Linter`.
- Reuse disabled/allow state without rereading or reparsing configuration.
- Pin one-load session ownership with a source contract.
- Follow-up: add bounded directory-to-manifest discovery caching.
## Completed tooling tranche: bounded manifest discovery

- Cache source/common-ancestor directory outcomes, including manifest misses.
- Consult cached ancestors before filesystem probes.
- Cap retained directory entries at 4096 and fall back to correct uncached discovery.
- Mark caller-prepared paths so lint policy resolution does not repeat the walk.
- Continue cloning policy before file-local attributes.
- Follow-up: extend parsed-policy caching from the adjacent-project slot to bounded unique manifests.
## Completed tooling tranche: bounded parsed-policy cache

- Replace the adjacent-only project-policy slot with a path-indexed flat cache.
- Retain at most 256 unique parsed manifests per command.
- Clone cached base policy before CLI and file-local overrides.
- Avoid struct-valued dictionary retrieval by storing integer indexes.
- Preserve uncached parsing after saturation.
- Follow-up: reuse `LintConfig.new()` defaults for manifest-free files without mutable sharing.
## Completed tooling tranche: shared manifest-free defaults

- Build the default lint-level dictionary once per command-owned `Linter`.
- Give each manifest-free file an isolated child configuration.
- Share immutable effective defaults while keeping overrides mutable per file.
- Pin absence of per-file `LintConfig.new()` in the no-manifest branch.
- Follow-up: reduce CLI argument policy rescans to one parsed command policy.
## Completed compiler tranche: storage-layout advisory indexing

- Replace growing-array field-ID deduplication with dictionary membership and an explicit count.
- Remove the redundant field-ID array allocation.
- Replace handwritten selection sort with the standard deterministic sort.
- Preserve identity format, completeness decisions, and overlap semantics.
- Follow-up: design a region-grouped interval sweep for overlap proof before changing the remaining pair analysis.
## Completed compiler tranche: remove incomplete string-builder rewrite

- Preserve the `Skeleton` class, factory, statistics, and identity entrypoint.
- Remove private concat candidate/rewrite machinery and unused loop-detector/local-ID state.
- Pin absence of push-only lowering with a source contract.
- Require typed builder construction, initialization, final joins, dominated use replacement, and semantic differential tests before rehabilitation.
- Follow-up: prefer CollectionPlan producer-consumer lowering once ownership/effect/cardinality facts are complete.
## Completed compiler tranche: close strength-reduction bypass

- Preserve provider metadata, class/factory compatibility, statistics, and zero-change receipts.
- Make direct function and block entrypoints identities while status is disabled.
- Remove signed arithmetic, decomposition, and synthetic-local rewrite helpers.
- Replace legacy transformation fixtures with fail-closed/source contracts in both test layouts.
- Follow-up: rehabilitate individual rewrite families only with per-operation range/type/overflow proofs and differential tests.
## Completed compiler tranche: remove unsafe dormant GVN

- Preserve the `Skeleton` class, factory, dependencies, statistics, and identity wrapper.
- Remove direct block-order value-numbering and cross-block rewrite entrypoints.
- Delete text-signature tables and unscoped field-load reuse.
- Pin absence of the block-order implementation with a source contract.
- Follow-up: rehabilitate only on dominators, structural keys, and MemorySSA-lite versions.
## Completed compiler tranche: close BCE direct-call bypass

- Preserve proof record types, counters, dependencies, factory, and compatibility methods.
- Make function and block entrypoints identities while status is disabled.
- Remove global loop-proof seeding, textual check keys, and direct instruction deletion.
- Replace simulated-elimination fixtures in both test layouts with fail-closed contracts.
- Follow-up: rehabilitate only with dominance-scoped SSA/range/mutation facts and differential safety tests.
## Completed compiler tranche: close general loop-transform bypasses

- Preserve LICM/unroller/combined classes, counters, thresholds, factories, dependencies, and identity compatibility methods.
- Remove preheader synthesis, predecessor redirection, instruction movement/duplication, and direct combined chaining.
- Remove per-instance loop detectors from disabled transforms.
- Replace simulated transformation fixtures in both test layouts with quarantine contracts.
- Follow-up: rehabilitate only on canonical LoopForest, SSA, MemorySSA-lite, effect and profitability facts.
## Completed compiler tranche: quarantine generator state-machine rewrite

- Preserve exported yield point/analysis types, discovery, class/factory/statistics, and identity methods.
- Remove dispatcher/signature/local/state-block construction and private segment lowering.
- Replace per-yield whole-function definition rescans with one forward definition walk plus conservative local snapshots.
- Pin separation of analysis and transformation with a source contract.
- Follow-up: move admitted coroutine lowering to an ABI/runtime owner backed by shared CFG liveness and ownership facts.

## Completed compiler tranche: quarantine body outlining

- Preserve exported compatibility analysis classes, counters, factory, and identity function/module entrypoints.
- Remove dormant cold-region grouping, liveness, CFG extraction/remapping, and synthetic-function construction.
- Pin absence of direct rewrite machinery with a source contract.
- Count the deletion as compiler parse/compile, allocation, and code-footprint reduction; do not claim runtime speedup without measurement.
- Follow-up: rehabilitate only with canonical region facts, complete SSA/ownership/unwind/debug proofs, checked module construction, profitability, and differential tests.

## Completed compiler tranche: quarantine local CSE

- Preserve exported expression/table/class/factory/statistics compatibility with fail-closed lookup and transform surfaces.
- Remove direct MIR rewrite, mutable leader selection, incomplete invalidation, and per-expression table operations from the Skeleton path.
- Pin absence of rewrite construction with a source contract.
- Record removed text hashing, dictionary churn, array cloning, and dead compiler source as compile-time/memory improvements without claiming runtime benefit.
- Follow-up: activate Copy-only local propagation first; then shared-semantics constant folding; rehabilitate CSE only with structural keys, ownership, kills, effects/traps, and MemorySSA-lite; defer DCE until observability and sparse-liveness budgets are proved.

## Completed tooling tranche: command-scoped lint CLI policy

- Parse deny/warn, output, fix, WM-lane, and profile options once per repository command.
- Pass a constant-size `LintCliPolicy` into each source invocation rather than the positional target array.
- Preserve standalone args wrappers and manifest → CLI → file-header precedence.
- Pin absence of per-file argument membership/profile scans with a source contract.
- Reduce explicit N-file policy work from quadratic argument comparisons to one linear command parse plus O(1) per file; retain only constant-size policy state.
- Follow-up: replace source-sized retained line arrays only after an explicit borrowing/ownership design.

## Completed compiler tranche: quarantine copy propagation

- Preserve exported `CopyChain`/`CopyPropagation` shapes, zero counters, factory, and identity wrapper.
- Remove partial block/instruction/operand/terminator rewrites and fixed-depth copy-chain walking.
- Replace simulated copy-to-move fixtures and their manual with honest fail-closed contracts.
- Record eliminated MIR-array rebuilding, chain traversal, dead parsing/compilation, and source footprint as compiler performance/memory improvements.
- Follow-up: implement exhaustive block-local Copy-only propagation with near-linear roots, ownership exclusion for Move, exact receipts, verification, and semantic differential witnesses.

## Completed compiler tranche: isolate legacy optimizer function state

- Reset constant, type, definition, use-count, and expression maps at every function entry, including the `None_` early return.
- Preserve cumulative statistics and configured optimization level.
- Add mirrored regressions proving all retained entries are released and statistics remain cumulative.
- Count prevention of cross-function `LocalId` contamination as correctness and release of retained MIR/dictionary state as memory hardening.
- Follow-up: remove the semantic HIR constant-fold no-op traversal; keep semantic constant evaluation and canonical MIR folding distinct.

## Completed compiler tranche: remove discarded HIR constant folding

- Delete the semantic HIR pass that rebuilt bodies but never installed them.
- Remove driver invocation and semantics-barrel exports; route `resolved_module` directly into bootstrap validation storage.
- Preserve semantic `const_eval` and canonical typed-MIR constant folding as distinct owners.
- Add mirrored source contracts for driver, barrel, removed file, and retained const evaluation.
- Count eliminated evaluator construction, function/expression traversal, and temporary HIR arrays as active compiler CPU/memory improvement.
- Follow-up: quarantine or rehabilitate the canonical MIR constant-fold direct method with shared arithmetic/result-type semantics.

## Completed tooling tranche: compact lint parsed-handoff state

- Build fallback source-location dictionaries during the existing canonical text-line traversal.
- Retain only function, collection-fix, and star-export location maps across parsing; remove full split-line state.
- Materialize config/index and release handoff state before AST diagnostic loops.
- Preserve defensive fallback indexing and all early-return releases.
- Pin absence of `last_source_lines` and immediate release with source contracts.
- Follow-up: evaluate result-array in-place compaction only after value-semantics/alias tests prove it safe.

## Completed compiler tranche: quarantine MIR constant folding

- Preserve evaluator, simplifier, pass, factory, method, statistics, and wrapper compatibility as zero-change/`nil` surfaces.
- Remove untyped host arithmetic, algebraic rewrites, branch rewrites, and unconditional MIR-array reconstruction.
- Replace direct-transform fixtures/manual with effective-pipeline and fail-closed contracts.
- Record deleted source/IR, avoided direct-call allocations, and malformed-result prevention as compiler performance/memory/correctness hardening.
- Follow-up: design one shared typed evaluator with exact target semantics, structured rejections, changed flags, receipts, verification, and differential tests.

## Completed tooling tranche: compact lint results in place

- Replace the second filtered result array with stable request-owned read/write compaction.
- Preserve ordering and construct isolated records only for severity changes.
- Truncate the tail after the captured original range is fully scanned.
- Pin `write <= read` algorithm shape and absence of the second buffer with source contracts.
- Reduce peak diagnostic reference/capacity retention without relying on mutable aliases.
- Follow-up: migrate remaining safe split-based lint wrappers to the canonical line view; preserve intentionally transformed/masked views.

## Completed compiler tranche: quarantine dead-code elimination

- Make every DCE transform entrypoint identity while status is `Skeleton`.
- Remove dense liveness construction, block/local scans, keep bitmaps and MIR
  rebuilding from the callable Skeleton path.
- Preserve mandatory probe classification as analysis-only compatibility and
  fail side-effect/purity decisions closed.
- Replace positive deletion fixtures/manual claims with quarantine contracts.
- Follow-up: separate `perf_facts_build_without_liveness` for production
  consumers that do not need dense liveness; rehabilitate DCE only with sparse
  liveness and exhaustive opcode semantics.

## Completed compiler/tooling tranche: scoped facts and linear diagnostics

- Add a named no-liveness PerfFacts builder and retain the verifier API as a
  compatibility alias.
- Migrate loop detection, auto-vectorization analysis, storage-access analysis,
  and typed-storage-view production away from dense liveness.
- Pin empty matrices/zero worklist behavior and the four production call sites.
- Replace human and JSON diagnostic evidence append loops with one join while
  preserving exact output ordering.
- Follow-up: introduce integrity-checked `PerfFactRequest` projections, and
  migrate the accessor-field lint from repeated source splits and
  `O(methods^2 + lines*methods)` scans to canonical source views and indexes.

## Completed tooling tranche: index accessor field rewrites

- Add line-based accessor-class parsing while preserving the source wrapper.
- Route the active fix registry through canonical lines and contexts.
- Replace repeated suffix and line-by-dummy scans with per-class dictionaries
  plus actual call-name extraction.
- Reuse canonical byte offsets and remove the redundant starts array.
- Preserve exact getter/setter rewrite guards and fail closed on ambiguous names.
- Follow-up: route the legacy aggregate easy-fix registry through one shared view
  and profile remaining rules that still accept raw source.

## Completed warning-system tranche: bound candidate and delimiter scans

- Reject non-public/extern lines before `primitive_api` item-suppression scans.
- Preserve file/item allow semantics and advance offsets once per line.
- Replace suffix-based spec-docstring counting with one absolute forward cursor.
- Remove duplicate silent-default warning entrypoints and pin one owner.
- Follow-up: implement dependency-closed `PerfFactRequest` presets so CFG-only
  and def-use-only analyses stop building unrelated fact families.

## Completed compiler tranche: request exact PerfFacts capabilities

- Add dependency-closed requests and diagnostics for hidden expansion.
- Keep full, no-liveness and verifier builders as compatibility wrappers.
- Migrate loop detection to CFG plus dominators without instruction def-use.
- Migrate storage access to def-use only and block-keyed vector/storage rewrite
  consumers to CFG+def-use without RPO/dominators.
- Keep every unrequested fact family empty and incomplete.
- Follow-up: expose requested/effective capabilities in optimization telemetry
  and replace the hard-coded liveness cell cap with a named budget policy.

## Completed review hardening: PerfFacts capability integrity

- Add explicit dominance completeness and gate loop discovery on it.
- Add CFG+def-use preset without RPO/dominance/liveness.
- Require CFG integrity for vector dependency analysis and typed-storage rewrite.
- Reject duplicate block identities before block-keyed def-use interpretation.
- Retain def-use-only storage-access analysis because incomplete facts become
  conservative unknown access rather than transformation authority.

## Completed tooling tranche: linearize wide-public deduplication

- Replace growing export-name array membership scans with a dictionary set.
- Maintain an explicit unique-export count rather than relying on dictionary
  length behavior.
- Preserve facade, wildcard, re-export, whitespace, comment and duplicate rules.
- Remove the single-use linear `list_has` helper.
- Follow-up: inventory remaining canonical lint dedupe arrays and distinguish
  count-only membership from ordering-sensitive result storage.

## Completed tooling tranche: skip inactive diagnostic policy work

- Guard serialized diagnostic code extraction with an explicit override count.
- Maintain the dictionary/count pair only at lint-config load and clear boundaries.
- Preserve suppression, severity rewriting, collection, and direct-print behavior.
- Avoid native dictionary length as a hot-path correctness predicate.
- Follow-up: replace serialized JSON policy projection with typed diagnostics.

## Completed compiler tranche: linear predecessor adjacency

- Replace per-edge dictionary array copyback with indexed owned buckets.
- Publish one predecessor array per distinct successor after edge discovery.
- Preserve edge multiplicity, predecessor order, dangling-edge evidence, and
  malformed-CFG counters.
- Pin a high-fan-in/duplicate-edge example plus a source regression guard.
- Follow-up: gate dense liveness allocation before matrix construction on every
  incomplete-input path.

## Completed tooling tranche: linear short-lambda discovery

- Replace recursive next-backslash discovery and prefix rescans with one pass.
- Preserve comment cutoff, quote toggling, eligibility, replacement ordering,
  and consumed-range suppression.
- Pin quoted, live, and commented backslashes plus absence of recursive helpers.
- Compute the functional-update boundary once rather than rescanning it for each
  candidate; continue inventorying syntax-dependent candidate parsers before
  claiming an end-to-end linear short-grammar rule.
- Follow-up: share a lightweight lexical line-state service across source rules
  instead of retaining rule-local quote/comment models.

## Completed compiler tranche: fail-fast liveness allocation

- Reject incomplete CFG/def-use inputs before live-in/live-out allocation.
- Skip USE/DEF allocation when duplicate locals already make def-use incomplete.
- Release USE/DEF working matrices when later validation fails closed.
- Preserve complete liveness results, visit budgets, and oversized-input status.
- Pin duplicate-local, uncovered-instruction, and dangling-edge empty-storage
  contracts.

## Completed tooling tranche: unchanged diagnostic identity fast path

- Compute CLI effective severity once per diagnostic.
- Return the immutable result directly when severity is unchanged.
- Rebuild only actual Warn-to-Deny transitions.
- Preserve text/JSON bytes, ordering, counts, fixes, evidence, and uncertainty.
- Follow-up: move policy projection before serialized output ownership entirely
  when typed diagnostic transport replaces compatibility JSON.

## Completed compiler tranche: linear loop-latch aggregation

- Index first-seen natural-loop headers into owned latch buckets.
- Deduplicate source/header edges with per-header membership dictionaries.
- Preserve loop order, backedge order, duplicate-edge coalescing, bodies, and exits.
- Remove dictionary-held growing-array extraction and copyback.
- Pin ordered multiple latches with a duplicate-target terminator.

## Completed tooling tranche: bounded fix assembly

- Stable-merge every replacement batch by descending start.
- Preserve equal-start insertion order through left-first equality.
- Assemble valid non-overlapping edits from source chunks with one join.
- Retain incremental behavior for negative, reversed, or out-of-range spans.
- Pin multi-edit output, equal-start insertion order, and invalid-span skipping.
- Replace per-file dictionary array copyback with owned indexed buckets while
  preserving dictionary key iteration and per-file replacement order.
- Consolidate ordering and assembly in the stdlib EasyFix owner.
- Delegate compiler FixToolApplicator and route lint fix through shared primitives.
- Remove every private and equal-start quadratic sort/repeated-splice implementation.

## Completed lint tranche: indexed SPIPE005 helper reachability

- Return typed bare-call names instead of delimiter-backed strings.
- Build local reverse-call buckets once and propagate through a queue.
- Preserve duplicate textual-name union, forward references, cycle semantics,
  and method-call exclusion.
- Add mirrored behavioral contracts for cycles, methods, and duplicates.
- Verification intentionally not run under the user's no-verify instruction.

## Completed structural-union symbol/narrowing tranche

- Add module-lifetime forward/reverse structural-union SymbolId maps to
  `SymbolTable`, reset, and codec transport.
- Recompute the preferred lane ID from canonical identity so caller hints
  cannot perturb assignments; bound collision probing and fall back to a
  unique ordinary ID without aliasing.
- Route enum and variant synthesis plus HIR narrowing through the same owner.
- Resolve bare named pattern types to their registered SymbolId and canonical
  member key.
- Build one key-to-variant dictionary per rewritten match.
- Correct nested-union member keys to shared ordered equality semantics.
- Deferred: generic/qualified type-pattern grammar and deep structured-key
  interning/streaming; pre-sorted preregistration for encounter-independent
  assignment under genuine FNV collisions.
- Verification intentionally not run under the user's no-verify instruction.

## Completed query outline-index tranche

- Build return-type and parameter-name facts together from the already-split
  source lines.
- Replace parallel-array linear call-site lookups with dictionaries while
  preserving first-definition/first-nonempty-return behavior.
- Make the former duplicate inlay module a narrow compatibility re-export.
- Add direct duplicate-precedence and source-ownership contracts.
- Deferred: cache parsed parameter vectors if profiling shows per-call splitting
  is material.
- Verification intentionally not run under the user's no-verify instruction.

## Completed formatter fingerprint tranche

- Replace immutable accumulator concatenation in token and comment-gap
  fingerprints with ordered fragments and one join.
- Preserve exact lexical-equivalence framing and failure behavior.
- Add comment-byte/order and source-shape regression contracts.
- Deferred: evaluate streaming fingerprint comparison only with representative
  measurement and exact mismatch semantics.
- Verification intentionally not run under the user's no-verify instruction.

## Completed CLOS001 scope-index tranche

- Use a prefix-maximum indentation index for exact prior-boundary lookup.
- Share incrementally advanced declaration counts across sibling closures with
  the same textual boundary and indentation.
- Preserve duplicate warning multiplicity, body/order/span, boundary quirks,
  and assignment syntax.
- Remove stale extra emitter arguments from query-check lint calls.
- Add production-path duplicate/sibling ordering and source-shape contracts.
- Deferred: replace overlapping nested-body scans with an offline assignment
  interval join while preserving legacy double reporting.
- Verification intentionally not run under the user's no-verify instruction.

## Completed structural-union canonicalization tranche

- Make member keys exhaustive and consistent with `hir_types_equal`.
- Use numeric text atoms and length-framed lists so canonical keys and sanitized
  variant identifiers cannot alias through delimiter/punctuation ambiguity.
- Replace linear deduplication and insertion rebuilding with dictionary dedup
  plus stable bottom-up merge ordering.
- Return one `UnionNormalized` result and reuse it in synthesis, registration,
  and narrowing.
- Replace linear module registration membership with a dictionary.
- Add direct permutation, flatten/optional, omitted-field, wrapper, and source
  complexity contracts.
- Track synthetic SymbolId collisions and named-type narrowing separately.
- Verification intentionally not run under the user's no-verify instruction.

## Completed diagnostic runtime tranche: fixed-pattern automaton

- Intern 116 fixed classifier literals into 1,160 sparse Aho-Corasick states.
- Scan each diagnostic byte string once into two local `u64` hit masks.
- Preserve all 80 ordered predicates, the negative `function` guard, explicit
  code precedence, shadowed rules, case sensitivity, and arbitrary dynamic
  codegen phrase behavior.
- Add mirrored every-literal, Unicode-neighbor, suffix-output, case, and
  no-match contracts.
- Retain one dynamic phrase search at its exact rule priority.
- Follow-up: add the deterministic Pure Simple generator and stale-data gate
  tracked in `doc/08_tracking/bug/query_error_matcher_generation_freshness_2026-08-22.md`.
- Verification intentionally not run under the user's no-verify instruction.

## Completed diagnostic tooling tranche: deterministic matcher generation

- Added the canonical append-only 116-pattern Pure Simple manifest.
- Added a bounded deterministic trie/failure/CSR/output-mask model builder.
- Added one-join source rendering, non-mutating exact `check`, and changed-only
  atomic `generate` modes without process, shell, C, or Rust delegation.
- Added mirrored manifest alignment, cardinality, exact source freshness, and
  injected-bound failure contracts.
- Added an 80-row postfix predicate manifest and seven-row fallback manifest.
- Added fail-closed priority, postfix arity, pattern-ID, E-code, and sole dynamic
  phrase validation plus exact generated-block freshness ownership.
- Completed direct constant-mask rule emission across low/high `u64` boundaries,
  removing about 135 helper calls and variable shifts on late/no-match paths.
- Remaining follow-up: stale-file CLI red fixture and executed latency/RSS
  evidence when verification is permitted.
- Completed bounded leading `Edddd` validation: reject non-`E` without a slice,
  then validate one five-byte candidate to avoid repeated raw-string `strlen`.
- Verification intentionally not run under the user's no-verify instruction.

## Completed diagnostic tranche: shared query error-code ownership

- Move the duplicated ordered classifier into cycle-free `query_error_codes`.
- Parameterize the legacy `FFI error` / active `SFFI error` distinction.
- Preserve malformed explicit codes, case sensitivity, overlap order, and exact
  error-kind fallbacks with mirrored contracts.
- Replace 473 entry-local lines with one 242-line owner plus four wrapper lines
  (net 227-line reduction).
- Completed next: replace the remaining fixed probes with an immutable sparse
  multi-pattern matcher without constructing a registry per call.
- Verification intentionally not run under the user's no-verify instruction.
