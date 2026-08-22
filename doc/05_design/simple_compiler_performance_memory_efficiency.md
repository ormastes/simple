<!-- codex-design -->
# Simple Compiler Performance and Memory Efficiency — Detail Design

## Scope

This design implements REQ-001..REQ-025 and NFR-001..NFR-015 as one staged program. It does not claim implementation or verification completion.

## Data model

### Pass integrity

`MirPassDescriptor` gains status, expectation, delegation, required/preserved/invalidated facts, and stable identity. Registry construction validates combinations. `EffectivePipelinePlanner` resolves names and backend policy before execution. Each pass returns `PassOutcome` containing original-or-new MIR, `MirChangeReceipt`, `PassRunRecord`, and verifier receipt when required. No partially mutated MIR escapes a failure.

Compiler self-rules include identity/empty active wrapper, missing/unchanged sentinel, invalid contract, dishonest effective listing, duplicate identity, missing run evidence, unenforced required fact, missing verifier receipt, and nondeterministic report order.

The verifier is admitted incrementally by named proof surface. The initial
`MirStructuralVerificationReceipt` proves block/local identity, canonical access coverage,
declared operand/local membership, signature-consistent ABI locals, entry membership, and CFG target closure only. It must
never be labeled a general MIR or semantic verifier.
Later receipts add opcode type rules, SSA dominance, ownership, loop-boundary,
and semantic-differential evidence. A pipeline-wide `--verify-each` claim requires all
applicable receipts, not merely the structural slice.

### Typed diagnostics

`PerfFactCollector` visits typed HIR once and indexes events by function, loop, call, receiver, value, region origin, and source span. Rules query indexes and `OperationSummaryRegistry`; they never reparse or recursively traverse the module independently.

`PerfRuleRegistry` owns stable code, group, tier, default kind/policy, fix support, and suppression. `PerfDiagnostic` projects to legacy V1 only for compatibility-owned rules and to deterministic V2 text/JSON/LSP. Exact source origin is mandatory; textual location recovery is removed per migrated rule.

During compatibility migration, `LintDiag.evidence_tier` is the single severity
input shared by CLI and query/LSP projections. `SourcePattern`,
`ParsedStructural`, and `Incomplete` performance diagnostics are warning-capped;
`TypedProven` follows profile policy. Human and JSON output carry the same stable
confidence, evidence, and uncertainty fields. The projection does no source read,
parse, hash, or tree traversal.

### Symbolic resources

`CostExpr` constructors flatten/sort/fold checked constants, cap depth/degree/variables/parts, and return `Unknown(BudgetExceeded)` rather than overflow. Expected, amortized, worst-case, total allocation, copied bytes, and peak-live bytes remain distinct.

`OperationSummary` covers receiver capability, time/resources, cardinality, access, order, uniqueness, laziness/enumeration, effects, and invalidation. Unknown user/foreign operations use top effects and unknown costs.

### MIR facts

`PerfFactsManager.for_function(MirRevision, MirFunction, AnalysisBudget)` returns a query facade. Fact construction is lazy and dependency-aware. Each result carries fingerprint, dependencies, counts, elapsed time, and budget. Cancellation is not cached; immutable incomplete results may be cached only for identical revision+budget.

CFG uses indexed successors/predecessors and cursor/deque worklists. Dominators use CFG order. LoopForest derives natural loops from dominance, retains multiple latches/exits, identifies irreducible loops, and never equates bound with trip count. Def-use includes terminators/phis; liveness uses bitsets; range proofs are dominance/program-point scoped. MemorySSA-lite versions regions and makes unknown writes clobber possibly aliased regions.

### Escape and COW

Escape finalization keeps unresolved sites `Unknown/MayEscape`. Production terminators/calls/stores/captures/suspensions feed proof paths. Field identity is base region + field, not guessed type/local. Stack eligibility requires closed flows, static/bounded size, alignment, frame budget, lifetime endpoint, and target policy.

Proposed COW MIR operations expose ensure/clone/mutate sites. Uniqueness transfer handles moves, aliases, calls, captures, returns, and joins. Profile counters share stable site IDs but cannot prove uniqueness.

## Rule evaluation

Tier 0 runs known high-confidence typed rules and suppresses fixed-small or unknown cases. Tier 1 adds MIR legality and remarks. Tier 2 uses bounded SCC summaries/affine solving and reports incomplete. Tier 3 correlates optional profiles.

Lint revision reuse is capability-bound, not a raw `[DeclId]` API. A
`LintParsedRevision` carries path, source digest, AST arena generation, and declarations.
The parsed lint entry checks all three identity dimensions before reading arena indices;
stale identity is a deny diagnostic, never a fallback parse or silent empty result.
Standalone lint owns exactly one parse and then calls the same parsed-results owner.

Fix applicability:

- Reserve and duplicate-lookup fixes require exact collection contract/mutation facts.
- Clone removal requires last-use, ownership, alias, effect, and destruction-order proof.
- Substring/view fixes require lifetime/escape proof.
- Representation/index/layout changes remain advisory unless public semantics and ABI are proven unchanged.

## Transform algorithms

Vector containment checks exact induction destination and `+1` constant first; until full dependence/alias/effect/target proof exists, the rewrite status is disabled and only analysis/remarks run.

CollectionPlan extracts producers, filters, mappings, reductions, materializations, cardinalities, callbacks, and ordering. Planner enumerates a bounded candidate set, proves legality, estimates resources, selects only positive plans, and records rejection reasons. Lowering uses true preheaders and preserves zero-trip behavior.

General fusion proves compatible lower/upper/step/order, dependence directions/distances, alias regions, effect/exception/destruction order, early exits, reduction numeric order, and profitability. Runtime alias versioning is Aggressive/profile-only and must preserve an unfused fallback.

Scalar passes rehabilitate in order: constant folding, copy propagation, DCE, local CSE, true LICM, reserve insertion, BCE, stack promotion, TCO, GVN; later string building, strength reduction, unrolling, fusion, and vector rewriting. Each activation is independent.

## Summary and profile formats

`PerfSummary` is fingerprinted by typed/MIR semantic hash, imported summaries, target layout, optimization config, and cost-model version. Bounded SCC propagation widens or returns incomplete. `.sperf` encodes deterministic static bounds/confidence/assumptions for CI diffs.

`.sprof-v2` is backward-compatible and adds optional typed records. Disabled instrumentation is compiled/branched out before allocations or I/O. Curve measurement uses >=4 sizes and repetitions, records distributions and startup subtraction, and never classifies from one timeout.

## Error handling

All analysis APIs use `AnalysisOutcome<T>`/`Result<T,E>`. Unknown and incomplete are data, not exceptions or optimistic defaults. Invalid pass/schema/config is an error before compilation. Verifier failure preserves pre-pass MIR, emits evidence, and stops. Cache mismatch discards/rebuilds once; repeated mismatch is explicit failure.

## Observability

Counters: parse/typed artifact builds/hits, fact builds/hits/rebuild reasons, nodes/edges/budget, pass candidates/transforms/rejections, instructions, elapsed, allocation/copy/COW bytes, summary invalidation, profile disabled/enabled activity. Stable IDs connect static and runtime evidence.

## Compatibility and rollout

Existing COLL behavior dual-runs during migration and must match ordered code/severity/span/fix/exit before ownership switches. Legacy JSON remains default until V2 admission. Pass rollback changes status to `Disabled(reason)` without deleting identity/schema. Existing `.sprof` v1 readers/writers remain supported.

## Verification mapping

REQ-001..005: pipeline/sentinel/verifier system and integration specs. REQ-006..009: revision reuse, exact spans, diagnostic compatibility. REQ-010..012: rule matrices and bounded costs. REQ-013..015: fact/invalidation/escape/COW adversarial tests. REQ-016..018: CollectionPlan/fusion/pass differential tests. REQ-019..023: summary/CI/profile/curve/hot-path measurements. REQ-024..025: facade guards, docs, traceability, and admitted pure-Simple provenance.

No UI design artifact is required: all surfaces are compiler CLI/LSP structured text/protocol outputs, covered by text/API/protocol evidence.
