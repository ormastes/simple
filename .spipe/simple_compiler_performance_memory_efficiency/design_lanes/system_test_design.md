# System-Test Design: Simple Compiler Performance and Memory Efficiency

## Scope and authority

This lane designs executable evidence for `REQ-001` through `REQ-025` and
`NFR-001` through `NFR-015`. It does not claim that an endpoint exists or that
any requirement passes. The final implementation and generated-manual review
remain owned by `/root`.

The tests must exercise pure-Simple production owners using an admitted
self-hosted binary. A Rust seed, source-string inspection, hand-built expected
record, or test-only reimplementation is not behavioral evidence. Missing
commands, facts, fixtures, or provenance fail closed.

## Canonical artifacts

| Evidence surface | Executable path | Generated/manual path | Purpose |
|---|---|---|---|
| Operator flow | `test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl` | `doc/06_spec/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.md` | The six frozen visible scenarios and end-to-end acceptance |
| Transform legality | `test/02_integration/compiler/optimizer_transform_integrity_spec.spl` | `doc/06_spec/02_integration/compiler/optimizer_transform_integrity_spec.md` | Sentinels, negative witnesses, verifier, idempotence, differential matrix |
| Diagnostic behavior | `test/02_integration/compiler/perf_diagnostic_contract_spec.spl` | `doc/06_spec/02_integration/compiler/perf_diagnostic_contract_spec.md` | Typed rules, compatibility, JSON/text, suppression and uncertainty |
| Shared facts and summaries | `test/02_integration/compiler/perf_facts_summary_spec.spl` | `doc/06_spec/02_integration/compiler/perf_facts_summary_spec.md` | Cache/revision/invalidation, escape, CostExpr, CollectionPlan and SCC summaries |
| Compile-time budgets | `test/05_perf/compiler/compiler_perf_facts_budget_spec.spl` | `doc/06_spec/05_perf/compiler/compiler_perf_facts_budget_spec.md` | Tier-0/Tier-1 latency, construction counts, RSS and determinism |
| Tool hot paths | `test/05_perf/compiler/compiler_tool_hot_path_spec.spl` | `doc/06_spec/05_perf/compiler/compiler_tool_hot_path_spec.md` | Warm lint/LSP/MCP startup/request scans, parses, subprocesses and RSS |
| Profile and curves | `test/05_perf/compiler/compiler_perf_profile_curve_spec.spl` | `doc/06_spec/05_perf/compiler/compiler_perf_profile_curve_spec.md` | `.sperf`, `.sprof-v2`, ranking and multi-size empirical curves |

No executable `.spl` may be copied below `doc/06_spec`. Docgen owns the Markdown
mirrors. Unit fixtures may live under
`test/fixtures/compiler/performance_memory_efficiency/`; durable baseline and
result receipts belong under a feature-specific evidence directory selected by
the implementation plan, never embedded as unexplained constants in a spec.

## Frozen executable interface

The umbrella spec displays these steps verbatim and in this order:

1. `Load the effective optimizer pipeline`
2. `Reject dishonest active transforms`
3. `Analyze one function with shared performance facts`
4. `Report actionable performance and memory diagnostics`
5. `Preserve semantics while applying a proven transform`
6. `Compare compiler and runtime evidence against the baseline`

The shared helpers are frozen:

- `setup_optimizer_integrity_fixture`
- `setup_perf_diagnostic_fixture`
- `check_effective_pipeline_status`
- `check_perf_facts_reuse`
- `check_perf_diagnostic_record`
- `check_semantic_differential`
- `check_perf_budget`

Setup helpers return explicit fixture/result objects; checker helpers return a
typed `Result` or assert concrete production output. Helpers must not synthesize
the behavior they check. Reusable setup is annotated `@inline`; every checker
used by a displayed scenario remains visible as a manual step or in complete
folded executable source.

## Umbrella scenarios

### 1. Load the effective optimizer pipeline

Exercise the real pipeline registry/dispatcher in text and machine modes.
Assert requested/effective separation, stable ordering, `PassStatus`,
`PassExpectation`, backend delegation, and disabled reasons. Edge fixtures mix
active, analysis-only, backend-delegated, and disabled passes. Error fixtures
use an unknown pass and a pass whose required facts are unavailable and assert
a nonzero/fail-closed result with a stable reason.

Primary trace: REQ-001, REQ-002, REQ-004, REQ-024; NFR-002, NFR-008,
NFR-009, NFR-014.

### 2. Reject dishonest active transforms

Run the compiler self-check over: a real active positive sentinel, a legal
non-candidate, an identity transform falsely marked active, an empty active
module transform, and the contained vectorizer. Assert candidate/transformed/
rejected counts and rejection codes. For each rehabilitated transform, execute
the applicable overflow, FP, trap, zero-trip, alias, exceptional control-flow,
unsafe-pointer, irreducible-CFG, and backend matrix exactly once. Run the
post-transform verifier and idempotence check.

Primary trace: REQ-001, REQ-003, REQ-005, REQ-017, REQ-018; NFR-001,
NFR-002, NFR-008, NFR-014.

### 3. Analyze one function with shared performance facts

Analyze a revisioned fixture twice and assert one CFG/predecessor/RPO build,
cache hits for downstream consumers, stable node/edge counts, and declared fact
preservation. Mutate MIR and assert only invalidated facts rebuild with a reason.
Exercise `Unknown` escape through return, aggregate, field/global, closure,
suspension, concurrency transfer, FFI/unknown call and variant paths; none may
become `NoEscape`. Exercise bounded CostExpr, operation summaries, CollectionPlan
and an SCC summary including explicit timeout/budget exhaustion.

Primary trace: REQ-006, REQ-009, REQ-012, REQ-013, REQ-014, REQ-015,
REQ-016, REQ-019; NFR-002, NFR-006, NFR-007, NFR-008, NFR-010.

### 4. Report actionable performance and memory diagnostics

Run the typed diagnostic endpoint over table-driven positive, suppression, and
uncertain fixtures. Cover the first-release rules and every catalog family in
REQ-011. Assert exact rule ID, severity versus remark class, primary/related
span, tier, confidence, symbolic evidence, fix applicability, suppression or
unknown reason, and deterministic text/JSON. Compatibility fixtures snapshot
COLL001-COLL008/COLL019 ordering, severity, exit status and suppression.
Fixed-small inner bounds and missing legality proofs must not produce a generic
multiple-loop warning. Unknown facts produce a remark/incomplete record, never
a transform or false warning.

Primary trace: REQ-007, REQ-008, REQ-010, REQ-011, REQ-012, REQ-015;
NFR-002, NFR-008, NFR-009.

### 5. Preserve semantics while applying a proven transform

Compile and execute paired optimized/unoptimized fixtures and compare exit,
stdout, stderr, result values, observable errors and applicable allocation/COW
counters. Positive cases include a pure CollectionPlan producer-consumer and a
rehabilitated scalar sentinel. Negative cases cover aliasing, effect/order,
zero-trip, early exit, exception/destruction order, numeric reduction order and
non-positive profitability. Rejected candidates must expose a precise missed
reason. A second optimization run must be idempotent.

Primary trace: REQ-005, REQ-014, REQ-015, REQ-016, REQ-017, REQ-018;
NFR-001, NFR-002, NFR-014.

### 6. Compare compiler and runtime evidence against the baseline

Validate provenance, then compare pinned before/after receipts for shared
frontend parsing, Tier-0/Tier-1 overhead, RSS, CFG construction, lint/LSP/MCP
warm requests, and the audited hot-path counters. Compare `.sperf` known,
regressed, improved and unknown summaries. Read `.sprof-v2` with profiling both
disabled and enabled, proving no disabled-path allocations/I/O and hotness-based
ranking without using profile data as legality proof. Run at least four input
sizes with repetitions for empirical curves; a single timeout must yield
incomplete evidence, not a complexity class.

Primary trace: REQ-020, REQ-021, REQ-022, REQ-023, REQ-024, REQ-025;
NFR-003 through NFR-015.

## Traceability and scenario depth

Each REQ receives at least three executable observations across the files above:
positive behavior, boundary/suppression behavior, and failure/unknown behavior.
The umbrella flow references the focused evidence rather than duplicating its
implementation.

| Requirement group | Positive evidence | Edge evidence | Failure evidence |
|---|---|---|---|
| REQ-001..005 | effective pipeline + valid sentinel | non-candidate/idempotence/backend matrix | dishonest identity, unavailable fact, verifier rejection |
| REQ-006..009 | one revision/session and indexed HIR facts | revision mutation and compatibility snapshot | stale artifact/reparse attempt/unknown fact |
| REQ-010..012 | each rule/catalog and known CostExpr | fixed bounds, expected/amortized/worst variants | unsupported operation and bounded `Unknown(reason)` |
| REQ-013..015 | cache reuse, proven escape/COW fact | targeted invalidation and lost uniqueness | unresolved escape and unsafe clone elimination reject |
| REQ-016..018 | pure plan/scalar transform | legal but unprofitable/idempotent candidate | alias/effect/control/numeric/adversarial rejection |
| REQ-019..022 | valid SCC, `.sperf`, `.sprof-v2`, curve | invalidation, disabled profile, coefficient change | timeout/stale profile/single-timeout classification reject |
| REQ-023..025 | measured repair, pure-Simple provenance, complete links | cold scan classified separately, Stage boundary | blocker record missing, Rust fallback, broken traceability |

NFRs are not satisfied by prose. NFR-001/002 use legality/differential tests;
NFR-003..007 and 010..013 use measurement receipts and counters; NFR-008/009
use byte-stable repeated output and compatibility fixtures; NFR-014 uses the
target matrix; NFR-015 uses the verification ledger proving no unchanged
criterion or identical failed command was rerun.

## Evidence classes and oracles

- **Behavioral:** returned typed records, exit status, stdout/stderr, diagnostic
  spans and stable reason codes from production endpoints.
- **Structural runtime:** verifier output, pass counters, cache construction and
  invalidation counters. Source inspection alone cannot satisfy these claims.
- **Semantic differential:** unoptimized versus optimized executions on the
  same generated inputs and target; equality covers all observable channels.
- **Performance:** before/after distributions, peak RSS and domain counters with
  commit, fixture and admitted binary hashes. One timing is never sufficient.
- **Profile:** valid `.sprof-v2` receipts and disabled-path probes; this ranks
  candidates but never authorizes a rewrite.
- **Documentation/trace:** docgen completeness, zero stubs, bidirectional REQ
  links, and retained manual claim-boundary prose.

Built-in matchers only: `to_equal`, `to_be`, `to_be_nil`, `to_contain`,
`to_start_with`, `to_end_with`, `to_be_greater_than`, and `to_be_less_than`.
Helper predicates must return concrete counts/records so specs do not hide
behavior behind tautological boolean assertions.

## Fail-fast scaffold policy

Before a production endpoint exists, its scenario body calls:

```simple
fail("implementation pending: REQ-NNN")
```

or `assert(false)` with the same requirement identifier. There are no
`pass_todo`, empty bodies, printed skips, fixture-only success records, or
always-true assertions. A missing binary, unsupported stage, timeout, absent
baseline, stale summary, malformed profile, unavailable backend, or docgen stub
is FAIL/BLOCKED evidence and cannot be converted to PASS. When an endpoint is
implemented, replace the placeholder with the real invocation and oracle in the
same change.

## Commands and execution order

Resolve and record the smallest applicable self-hosted pure-Simple runtime once;
the examples below use `<admitted-simple>` deliberately and must not silently
fall back:

```sh
SIMPLE_LIB=src <admitted-simple> check test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl
SIMPLE_LIB=src <admitted-simple> test test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/02_integration/compiler/optimizer_transform_integrity_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/02_integration/compiler/perf_diagnostic_contract_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/02_integration/compiler/perf_facts_summary_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/05_perf/compiler/compiler_perf_facts_budget_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/05_perf/compiler/compiler_tool_hot_path_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/05_perf/compiler/compiler_perf_profile_curve_spec.spl --mode=interpreter
```

Run each applicable test/measurement once after its implementation stabilizes.
Then run docgen once per executable spec:

```sh
<admitted-simple> spipe-docgen <spec> --output doc/06_spec --no-index
```

Every invocation must report complete with `0 stubs`. Final layout gate:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```

It must print `0`. The final verifier additionally runs the repository-required
compiler/core/lib, MCP/LSP, facade guards, owned-file lint/duplicate checks and
optimizer-sentinel integrity commands exactly once as recorded in the canonical
verification plan.

## Manual visibility review

The generated umbrella manual must show the six frozen steps as the primary
reader flow, in order. It explains requested versus effective pipeline state,
why a transform was rejected, which shared facts were reused, why a diagnostic
is actionable or suppressed, what semantic channels were compared, and what
the baseline proves. Fixture setup and large adversarial matrices are folded;
critical rejection reasons, evidence provenance, and all claim boundaries stay
visible. The focused manuals expose their behavioral tables and commands rather
than dumping raw fixture source.

Manual acceptance requires: all referenced helpers visible or present in
folded executable source; every REQ link resolves; measurement tables include
provenance; incomplete/blocked rows are labeled; no static inventory is
presented as runtime evidence; and independent `/root` review records manual
quality before verification can report PASS.

## Design handoff gates

1. Canonical architecture assigns production owners for every helper endpoint.
2. The implementation plan assigns fixture, spec, measurement and manual owners.
3. Shared reason codes and JSON schema are frozen before fixtures are authored.
4. Baselines are captured before performance changes with full NFR-011 provenance.
5. A highest-capability review accepts all generated scenarios and exclusions.
6. Release remains forbidden until every selected requirement has current,
   non-placeholder evidence and verification reports `STATUS: PASS`.
