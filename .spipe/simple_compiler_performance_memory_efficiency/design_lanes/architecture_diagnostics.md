<!-- codex-architecture -->
# Diagnostic and Pass-Integrity Architecture Lane

## Scope and decision

This lane designs the contracts that make performance diagnostics and optimizer activation truthful. It covers pass status/expectation/run evidence, effective-pipeline planning, performance rule identity and diagnostics, operation/resource summaries, text/JSON compatibility, warning/error versus optimization remarks, CLI surfaces, exact spans, suppression, and compiler self-lints. It does not design MIR fact algorithms, CollectionPlan lowering, profiling storage, or individual optimization implementations except where their interfaces cross this slice.

The architecture has two shared contract capsules:

1. `src/compiler/00.common/diagnostics/` owns versioned diagnostic interchange and rendering-independent source evidence.
2. `src/compiler/60.mir_opt/mir_opt/` owns pass descriptors, effective-pipeline planning, transform evidence, and optimizer-integrity findings.

Typed performance rule collection belongs in `src/compiler/35.semantics/perf/`; the lint CLI and compiler driver are adapters. There must not be a second performance diagnostic model in `src/compiler/90.tools/lint/` or a second pass registry in a CLI application.

## Existing boundaries to preserve

| Existing owner | Current responsibility | Migration constraint |
|---|---|---|
| `src/compiler/00.common/diagnostics/diagnostic_v1.spl` | Canonical rich diagnostic with stable code, spans, related labels, fixes, and JSON | Extend additively through a V2 envelope; do not fork rendering contracts into lint/perf modules. |
| `src/compiler/00.common/diagnostics/span.spl` | Canonical byte-offset and line/column span | Performance diagnostics carry this exact span from parser/HIR/MIR source maps; textual line search is forbidden. |
| `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` | Legacy `LintDiag`, profile configuration, source attributes | Preserve `COLL001`-`COLL008`/`COLL019` behavior while adapting new typed diagnostics at one boundary. |
| `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl` | Legacy text/JSONL rendering and exit counts | Remains the compatibility adapter until all legacy rules are baselined. JSONL stdout stays pure. |
| `src/compiler/60.mir_opt/mir_opt/mod.spl` | `PassKind`, `MirPassDescriptor`, registry, requested pipelines, backend plan, dispatch | Becomes the single registry and effective-pipeline planner; unknown names cease silently returning unchanged input. |
| `src/compiler/80.driver/driver_pipeline_passes.spl` | Driver pipeline orchestration | Consumes an immutable effective plan and run records; does not reinterpret pass status. |
| `src/compiler/70.backend/backend/optimization_passes.spl` | Backend optimization ownership | Reports delegation decisions by stable pass identity without impersonating a Simple MIR transform. |

## Module layout

Proposed files are new unless marked existing:

```text
src/compiler/00.common/diagnostics/
  diagnostic_v1.spl                 # existing compatibility schema
  diagnostic_v2.spl                 # versioned common envelope
  diagnostic_v2_schema.sdn          # machine schema
  diagnostic_kind.spl               # user diagnostic vs optimization remark
  diagnostic_evidence.spl           # confidence, tier, resource evidence
  diagnostic_render_text.spl        # deterministic human projection
  diagnostic_render_jsonl.spl       # deterministic JSONL projection

src/compiler/35.semantics/perf/
  rule_id.spl                        # PerfRuleId registry and stable groups
  diagnostic.spl                     # PerfDiagnostic domain object
  operation_summary.spl              # OperationSummary contracts
  cost_expr.spl                      # bounded canonical CostExpr
  suppression.spl                    # effective policy and rationale
  collector.spl                      # single typed-HIR event collector boundary

src/compiler/60.mir_opt/mir_opt/
  mod.spl                            # existing PassKind/registry entry point
  pass_contract.spl                  # PassStatus/Expectation/Delegation
  pass_run_record.spl                # immutable per-run evidence
  effective_pipeline.spl             # request resolution and fail-closed plan
  pass_integrity_lint.spl            # compiler-only COMP-PERF rules
  pass_report.spl                    # text/JSON report projection

src/compiler/80.driver/
  driver_pipeline_passes.spl         # existing consumer of EffectivePipeline
  driver_diagnostics.spl             # common diagnostic routing

src/compiler/90.tools/lint/_LintMain/
  perf_adapter.spl                   # PerfDiagnostic -> legacy compatibility
  config_and_model.spl               # existing config, staged migration
  entry_and_fixes.spl                # existing CLI rendering compatibility
```

Layering is one-way: `00.common` knows no lint or optimizer concepts; `35.semantics/perf` imports common diagnostics; `60.mir_opt` imports common diagnostics and shared resource contracts but does not import the lint CLI; `80.driver` composes them; `90.tools/lint` adapts them. Sibling-private implementations communicate only through these shared contracts.

## Pass contracts

### Data model

```text
enum PassStatus:
    Active
    AnalysisOnly
    RemarkOnly
    Skeleton
    Disabled(reason: text)

enum PassExpectation:
    MayTransform
    MustTransformSentinel(sentinel_id: text)
    NeverTransforms

enum BackendDelegation:
    None
    Delegated(backend: text, reason: text)
    BackendMayRepeat(backend: text, reason: text)

struct MirPassDescriptor:
    stable_name: text
    aliases: [text]
    provider: OptimizationRuleProvider
    kind: PassKind
    scope: PassScope
    cost_class: text
    status: PassStatus
    expectation: PassExpectation
    backend_delegation: BackendDelegation
    required_facts: [PerfFactKind]
    preserves: [PerfFactKind]
    invalidates: [PerfFactKind]

struct PassRunRecord:
    schema_version: i64
    run_sequence: i64
    requested_name: text
    stable_name: text?
    status: PassStatus?
    expectation: PassExpectation?
    backend_decision: MirPassBackendDecision?
    outcome: PassRunOutcome
    functions_seen: i64
    candidates: i64
    transformed: i64
    rejected: i64
    instructions_before: i64
    instructions_after: i64
    elapsed_ns: i64
    rejection_counts: Dict<PassRejectionReason, i64>
    verification: PassVerificationRecord?
```

`PassRunOutcome` is `Transformed | UnchangedNoCandidate | UnchangedRejected | AnalysisProduced | RemarkProduced | SkippedDisabled | SkippedSkeleton | Delegated | Failed`. Rejection reasons are a closed enum with stable machine names (`missing_fact`, `alias_unknown`, `effect_unknown`, `range_unproved`, `not_profitable`, `target_illegal`, `budget_exhausted`, `verification_failed`) plus `Other(detail)` for forward-compatible human detail. Counts must satisfy `candidates = transformed + rejected`; unknown-name resolution has no fabricated candidate count.

### Effective pipeline

```text
RequestedPipeline
  -> resolve aliases through mir_pass_descriptor_registry()
  -> reject unknown/ambiguous names
  -> apply PassStatus
  -> check required facts and configured budgets
  -> apply backend policy/delegation
  -> produce EffectivePipeline(entries, exclusions, errors)
  -> execute only EffectiveEntry.RunTransform/RunAnalysis/RunRemarks
  -> emit one PassRunRecord for every requested entry
```

`EffectivePipelineEntry` keeps request order and occurrence index because cleanup passes can legitimately appear more than once. It records requested spelling, stable name, status, execution mode, backend decision, and exclusion reason. `Skeleton` and `Disabled` never dispatch. `AnalysisOnly` and `RemarkOnly` may execute but cannot report `Transformed`. `Active + NeverTransforms` is invalid. `AnalysisOnly/RemarkOnly + MustTransformSentinel` is invalid. Backend delegation is independent of implementation status: a disabled Simple transform may be delegated, but the report must say `disabled + delegated`, never `active`.

Unknown pass names, duplicate aliases, unavailable mandatory facts, invalid descriptor combinations, and an effective plan containing an unsafe contained pass are planning errors. They fail compilation/configuration before dispatch; they do not return the original MIR as success.

### Effective pipeline output

Text output (`--print-effective-pipeline`) is stable and compact:

```text
requested speed[14] auto_vectorize
effective excluded status=disabled reason=induction_and_dependence_proofs_unavailable
backend llvm delegated reason=llvm_runs_vectorizer_pipeline
```

Machine output (`--emit-opt-report=jsonl`) uses versioned records:

```json
{"schema":"simple.opt-report","version":1,"type":"pipeline-entry","sequence":14,"requested":"auto_vectorize","stable_name":"auto_vectorize","status":"disabled","effective":"excluded","reason":"induction_and_dependence_proofs_unavailable","backend":{"name":"llvm","decision":"delegated","reason":"llvm_runs_vectorizer_pipeline"}}
```

Ordering is requested pipeline order, then function stable identity, then candidate source/MIR position, then rejection-reason enum order. Timing is evidence but never participates in ordering or semantic cache keys.

## Diagnostic and resource contracts

### Stable rule identity

`PerfRuleId` is a closed typed identity whose renderer returns a stable code such as `COLL010`, `COPY001`, `MEM001`, `LOOP001`, or `COMP-PERF001`. The registry entry owns:

```text
struct PerfRuleDescriptor:
    id: PerfRuleId
    code: text
    group: PerfRuleGroup
    default_policy: Dict<LintProfile, DiagnosticPolicy>
    tier: AnalysisTier
    default_kind: PerfDiagnosticKind
    supports_fix: bool
    suppressible: bool
```

Groups are at least `performance`, `complexity`, `allocation`, `copy`, `layout`, `retention`, `optimizer_integrity`, and `remarks`. Codes are never inferred with string prefix tests at the configuration boundary; the registry is exhaustive and CI checks duplicate/missing codes.

### Warning/error versus remarks

```text
enum PerfDiagnosticKind:
    SourceDiagnostic       # policy maps to allow/warning/error and exit status
    RemarkPassed           # never affects normal lint/build exit status
    RemarkMissed
    RemarkAnalysis
    RemarkFailure          # compiler optimization failure; exit only by explicit policy
    CompilerIntegrity      # compiler CI/configuration error, never a user source lint
```

Source diagnostics identify actionable source-level problems. Missed optimizer opportunities caused by aliases, effects, unavailable facts, or cost are remarks. `CompilerIntegrity` findings are emitted by compiler self-lints against compiler configuration/implementation and cannot be suppressed by source attributes. Parse/type failure remains a normal compiler diagnostic and prevents performance certification; it is not downgraded to `AnalysisIncomplete`.

### `CostExpr`

```text
enum CostExpr:
    Zero
    Constant(i64)
    SizeOf(CostSymbol)
    Add([CostExpr])
    Multiply([CostExpr])
    Maximum([CostExpr])
    Log2(CostExpr)
    Expected(CostExpr)
    Amortized(CostExpr)
    Unknown(UnknownReason)
```

Construction is private to `cost_expr.spl`. Public constructors canonicalize: flatten associative nodes, remove identities, sort operands by stable structural key, fold checked constants, deduplicate `Maximum`, cap depth/degree/variables/parts, and return `Unknown(BudgetExceeded(...))` on overflow or a cap. `Unknown` dominates claims that require a bound; it is never simplified to zero or constant. Expected, amortized, and worst-case claims remain distinguishable in text and JSON.

### `OperationSummary`

```text
struct OperationSummary:
    operation_id: text
    time_worst: CostExpr
    time_expected: CostExpr?
    allocation_count: CostExpr
    allocation_bytes: CostExpr
    peak_live_bytes: CostExpr?
    output_cardinality: CostExpr
    effects: EffectSummary
    access: AccessKind
    order: OrderContract
    uniqueness: UniquenessContract
    laziness: LazinessContract
    enumeration: EnumerationContract
    invalidation: InvalidationContract
    confidence: EvidenceConfidence
```

Unknown user/foreign operations receive explicit unknown fields and top effects. They never inherit constant, pure, non-allocating, or single-enumeration defaults. Standard-library summaries are generated/versioned with the library build; inferred summaries carry the typed-HIR/MIR semantic fingerprint and imported-summary hashes.

### `PerfDiagnostic`

```text
struct PerfDiagnostic:
    rule: PerfRuleId
    kind: PerfDiagnosticKind
    message: text
    primary: SourceEvidence
    related: [RelatedEvidence]
    configured_policy: DiagnosticPolicy
    effective_policy: DiagnosticPolicy
    profile: LintProfile
    tier: AnalysisTier
    confidence: EvidenceConfidence
    cost_before: CostExpr?
    cost_after: CostExpr?
    allocation_bytes: CostExpr?
    copied_bytes: CostExpr?
    cardinality: CostExpr?
    hotness: ProfileEvidence?
    rejection_reason: PassRejectionReason?
    incomplete: AnalysisIncomplete?
    fixes: [DiagnosticFix]
    suppression: SuppressionDecision
```

`SourceEvidence` contains canonical `Span`, module revision/fingerprint, and stable node or MIR origin. The primary span is mandatory for a source diagnostic; a remark may use a function/module anchor when generated MIR has no finer source origin. Related spans explain receiver, loop, allocation, alias, or call evidence. No adapter searches source text to recover a line.

## Versioned rendering and compatibility

`PerfDiagnostic` is a domain object, not a renderer. It projects to `DiagnosticV2`, which wraps compatible `DiagnosticV1` fields plus typed extensions. `DiagnosticV1` remains readable and renderable during migration.

### Text

Existing `COLL001`-`COLL008`/`COLL019` continue through `LintDiag` and retain exact severity, order, fixes, suppression behavior, and exit counting until a rule-specific baseline approves migration. New typed rules use the common text renderer but match the existing leading form:

```text
path:line:column: warning[COLL010]: repeated linear lookup inside a dynamic loop
```

Evidence appears as indented notes in a deterministic order. Remarks lead with `remark[LOOP001/missed]` and are emitted only when requested. They never increment legacy warning/error counts.

### JSONL

Legacy `--json` remains schema-compatible for old lint records. New `--diagnostic-format=jsonl-v2` and optimizer reports emit a versioned superset. Each line is one complete JSON object; logs and summaries use stderr unless they are declared JSON record types. Required V2 fields are `schema`, `version`, `type`, `kind`, `code`, `message`, `primary`, `configured_policy`, `effective_policy`, `profile`, `tier`, `confidence`, and `suppression`. Optional cost/profile/fix fields are omitted rather than encoded with ambiguous sentinel values.

Stable JSON object key order is schema order; arrays are pre-sorted by semantic order. Unknown enum values are rejected by strict readers and preserved as raw names by tolerant readers. Unsupported schema major versions fail explicitly. A renderer failure produces a minimal valid `diagnostic-render-failure` JSON record on stdout and the detailed error on stderr; it must never leak partial JSON.

## Suppression and policy

Resolution order is:

```text
rule default for profile
  -> project group policy
  -> project exact-rule policy
  -> file/module group attribute
  -> file/module exact-rule attribute
  -> CLI --deny-all / explicit rule override
  -> effective policy + SuppressionDecision provenance
```

`SuppressionDecision` is `NotRequested | Applied(scope, configured_by, reason?) | Rejected(reason)`. Exact rule beats group at the same scope; narrower source scope beats project scope. Remarks are opt-in filters, not lint severity promotions. Intentional Cartesian products or protocol-bounded loops use typed facts/annotations that alter evidence, not broad suppression. Compiler-integrity findings, parse failures, schema failures, and analysis-incomplete certification failures are non-suppressible. Deny-level source suppression requires a recorded rationale in robust/critical policy.

The registry extends `all_lint_names()` and `map_lint_code_to_config_name()` through typed iteration rather than hand-maintained `COLL*` branches. Legacy string names remain aliases. Unknown configuration names fail with a configuration diagnostic instead of silently leaving a finding unchanged.

## CLI surfaces

| Surface | Behavior |
|---|---|
| `simple check` | Runs high-confidence typed source diagnostics; remarks off; existing exit behavior preserved. |
| `simple lint` | Thin session owner over cached parsed/typed artifacts; compatibility text/JSON by default; `--diagnostic-format=jsonl-v2` opts into V2. |
| `simple build -O2 --remarks=perf` | Emits passed/missed/analysis/failure records selected by stable group/pass filters; remarks do not fail build unless explicit `--remark-failure-policy=error`. |
| `simple build --print-effective-pipeline` | Prints requested/effective/delegated/excluded entries without executing an extra compilation. |
| `simple build --emit-opt-report=text|jsonl` | Emits effective pipeline and `PassRunRecord` evidence. JSONL stdout is pure. |
| `simple build --verify-each` | Test/developer mode verifier after every changed transform; verifier failure names the pass and stops downstream transforms. |
| `simple perf --deep` | Consumes the same diagnostics/summaries, adds bounded interprocedural evidence, and reports incomplete analyses explicitly. |
| LSP | Publishes source diagnostics only by default; requested remarks use a separate capability/result set and stable IDs for replacement. |

Unknown flags, invalid filter names, unknown passes, incompatible schema requests, and contradictory output destinations fail before compilation. If text and JSON are both requested to stdout, configuration fails; the caller must direct one stream to a file.

## Compiler self-lints

`src/compiler/60.mir_opt/mir_opt/pass_integrity_lint.spl` runs over descriptors plus sentinel manifests and emits non-user `CompilerIntegrity` diagnostics:

| ID | Condition |
|---|---|
| `COMP-PERF001 registered_transform_is_identity` | Active transform wrapper is structurally unconditional identity or module loop is empty. |
| `COMP-PERF002 active_transform_missing_sentinel` | Active `MustTransformSentinel` has no resolvable fixture. |
| `COMP-PERF003 transform_sentinel_unchanged` | Positive sentinel reports `changed=false` or zero transforms. |
| `COMP-PERF004 invalid_pass_contract` | Status, expectation, scope, or delegation combination violates invariants. |
| `COMP-PERF005 pipeline_advertises_non_effective_pass` | User-visible effective list says active/run while planner excludes it. |
| `COMP-PERF006 unknown_or_duplicate_pass_identity` | Stable name/alias is missing, duplicated, or resolves ambiguously. |
| `COMP-PERF007 transform_missing_run_evidence` | Executed active transform omits counters, instruction delta, or stable rejection evidence. |
| `COMP-PERF008 required_fact_not_enforced` | Descriptor requires a proof fact but dispatch can execute without it. |
| `COMP-PERF009 changed_pass_not_verified` | Verification policy requires a check but changed output lacks a verifier receipt. |
| `COMP-PERF010 nondeterministic_report_order` | Registry/pipeline/report order differs for identical admitted inputs. |

Static wrapper checks are only the first gate; sentinel execution is authoritative. A transform may legitimately be unchanged for normal inputs. `MayTransform` is allowed only temporarily for an active transform with a documented non-sentinel contract; release policy should converge rehabilitated transforms to `MustTransformSentinel`.

## Data flows

### Source diagnostic flow

```text
shared CompilerSession(revision)
  -> parsed module + typed HIR + exact source map
  -> one PerfFactCollector traversal
  -> indexed events + OperationSummary lookup
  -> rule evaluator returns PerfDiagnostic
  -> suppression/policy resolver
  -> deterministic sort
  -> DiagnosticV2
  -> text / JSONL / LSP adapters
  -> legacy LintDiag adapter only for compatibility-owned rules
```

If parse/type facts are unavailable, performance rules do not fall back to name guessing. Existing explicitly source-only rules may run through their legacy owner, while the typed tier returns `AnalysisIncomplete` evidence and never certifies absence of findings.

### Optimizer flow

```text
OptLevel + requested pass overrides + target/backend
  -> registry resolution
  -> EffectivePipeline (or planning failure)
  -> shared PerfFacts admission
  -> pass candidate discovery
  -> transform/analysis/remark
  -> verify changed IR when policy requires
  -> invalidate declared facts
  -> immutable PassRunRecord
  -> opt-report renderer + compiler self-lint receipts
```

On transform failure, preserve the input MIR snapshot/fingerprint, identify the pass and candidate, emit `RemarkFailure` plus compiler error according to mode, and stop that pipeline. Never continue with partially changed MIR. Production builds fail closed for verifier failure; developer fuzzing may save both inputs and then terminate.

## Migration plan

1. Add common enums/envelopes and golden V1/V2 text+JSON tests without changing callers.
2. Extend `MirPassDescriptor` constructors and every registry entry with explicit status, expectation, delegation, required/preserved/invalidated facts. Initially mark observed identities honestly and contain unsafe `auto_vectorize` rewriting.
3. Replace name lookup duplication with one registry-derived index; build and print `EffectivePipeline`; make unknown names a planning error.
4. Add `PassRunRecord` and adapt existing `PassStatistics` as a derived aggregate, not an independent source of truth.
5. Add compiler self-lints and positive/negative sentinel manifest. Make integrity failures release-blocking.
6. Add `PerfRuleId`, registry, `CostExpr`, `OperationSummary`, and `PerfDiagnostic`; register configuration groups without enabling new rules.
7. Add exact source-origin transport from shared parser/HIR/MIR source maps and eliminate textual location recovery for each migrated rule.
8. Migrate one existing COLL rule at a time behind dual-run comparison. Require same ordered code/severity/span/fix/exit result before switching ownership; delete the old implementation after its baseline passes.
9. Enable new high-confidence typed rules. Unknown or fixed-small-bound cases suppress findings with recorded rationale.
10. Add opt-in remarks and deep-analysis projections after stable source diagnostics and machine schemas are admitted.

Rollback is per registry entry: typed rule ownership can return to `LegacyAdapter`, and a transform status can become `Disabled(reason)` without changing stable identity or output schema. Rollback never removes evidence fields or re-advertises a disabled transform.

## Invariants and error handling

1. One stable registry entry per pass and per performance rule.
2. Requested pipeline is immutable evidence; effective pipeline is a separate immutable plan.
3. No `Skeleton`/`Disabled` dispatch; no transform outcome from analysis/remark-only entries.
4. A changed transform has verifier evidence when verification is enabled, exact before/after instruction counts, and declared fact invalidation.
5. Missing facts, timeouts, cancellation, stale summaries, unknown calls, and renderer/schema mismatch are explicit; none implies safety or absence of a problem.
6. Source warnings/errors have exact primary spans. Text search is never a source-location mechanism.
7. Remarks do not alter normal source-lint exit status. Compiler-integrity errors are not user lints.
8. Existing COLL observable behavior is frozen until rule-specific migration evidence exists.
9. JSONL stdout contains JSON records only and remains deterministic.
10. Fix applicability never exceeds proof confidence; representation/ownership-changing suggestions are advisory unless equivalence is proven.
11. Suppression decisions retain provenance, and non-suppressible failures remain visible.
12. Caches and reports are revision-, target-, configuration-, and cost-model-bound; stale evidence is rejected.

## Requirement traceability

| Requirement | Architecture evidence in this lane |
|---|---|
| REQ-001 | Effective-pipeline containment excludes unsafe active vector rewriting while retaining separately labeled analysis/remarks. |
| REQ-002 | `PassStatus`, `PassExpectation`, and independent `BackendDelegation`. |
| REQ-003 | Sentinel contract, `PassRunRecord`, stable rejections, and `COMP-PERF001`-`003`/`007`. |
| REQ-004 | Immutable requested/effective plans, fail-closed resolution, text/JSON pipeline output. |
| REQ-005 | Verification receipt and failure rollback/termination semantics. |
| REQ-006 | `CompilerSession(revision)` source flow and thin lint adapter. |
| REQ-007 | `PerfRuleId`, `PerfDiagnostic`, kinds, spans, evidence, fixes, suppression, V2 output. |
| REQ-008 | Legacy adapter, frozen COLL behavior, dual-run migration. |
| REQ-009 | Single HIR collector boundary and MIR-only authoritative alias facts. |
| REQ-010/REQ-011 | Central extensible rule registry, tier/kind/action policy, unknown/fixed-bound suppression. |
| REQ-012 | Bounded canonical `CostExpr` and complete `OperationSummary`. |
| REQ-013 | Required/preserved/invalidated fact declarations at pass boundary. |
| REQ-014 | Unknown external operation/effect/escape evidence fails closed. |
| REQ-015 | Copy/allocation evidence fields and proof-bounded fix applicability. |
| REQ-016/REQ-017 | Remarks and rejection reasons preserve unknown legality/profitability instead of guessing. |
| REQ-018 | Per-pass rehabilitation status, sentinel, differential/verification evidence interfaces. |
| REQ-019/REQ-020 | Versioned confidence/unknown resource evidence and deep/CI diagnostic kind. |
| REQ-021/REQ-022 | Optional hotness/profile fields that prioritize but never prove semantics. |
| REQ-023 | One registry/index, shared parse facts, no textual span recovery or repeated pass-name scans. |
| REQ-024 | Pure-Simple owners and existing compiler/backend facade boundaries. |
| REQ-025 | Stable IDs and machine evidence support executable traceability. |

| NFR | Architecture evidence in this lane |
|---|---|
| NFR-001 | Active transform sentinels, verifier receipts, and fail-stop rollback. |
| NFR-002 | `Unknown`/`AnalysisIncomplete` and explicit planning/rendering failures. |
| NFR-003/NFR-004 | One collector, registry-derived indexes, opt-in remarks, derived statistics. |
| NFR-005/NFR-006 | Revision-owned session evidence; no separate parse or unbounded diagnostic cache. |
| NFR-007 | Pass fact preservation/invalidation and rebuild reasons in run evidence. |
| NFR-008 | Stable ordering and version-bound deterministic records. |
| NFR-009 | Frozen legacy behavior and versioned additive JSONL migration. |
| NFR-010 | Bounded `CostExpr`, explicit incomplete evidence, selective deep mode. |
| NFR-011 | Run records retain pass, target/backend/config and timing provenance hooks. |
| NFR-012 | Profile evidence is optional and absent paths need no allocation/I/O. |
| NFR-013 | Shared session adapter prevents tool-server reparsing/subprocess paths. |
| NFR-014 | Backend delegation and target data are injected through existing owners. |
| NFR-015 | Sentinel/golden evidence is one-shot and deterministic; no architecture requirement asks for retry loops. |

## Parallel ownership handoff

Sidecar lane: this file is the diagnostics/pass-integrity lane. It assumes separate lanes own MIR facts, CollectionPlan/transforms, tool hot paths, and system-test design. Merge owner: root SPipe design agent. Final reviewer: normal/highest-capability architecture reviewer. Shared interface names that other lanes must use are `PassStatus`, `PassExpectation`, `BackendDelegation`, `PassRunRecord`, `EffectivePipeline`, `PerfRuleId`, `PerfDiagnostic`, `OperationSummary`, `CostExpr`, and `AnalysisIncomplete`; alternate parallel types must be reconciled into these owners rather than retained as siblings.
