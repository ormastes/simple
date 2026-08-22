# Lint and performance-diagnostics research lane

Scope: static source audit at `37bd406e219cc35cae049b4130f5167c21801864`.
No compiler, lint, test, or benchmark execution was performed. “Observed” below
means directly present in source; runtime or compile-time consequences remain to
be measured unless linked to an existing measured bug report.

## Current architecture

- The public lint command discovers files and invokes `run_lint_file` once per
  file (`src/app/io/cli_lint_commands.spl:169-205`). SIMD opportunities are a
  separate source pass with `info` output and never affect exit status
  (`src/app/io/cli_lint_commands.spl:206-221`).
- `lint_cli_source` first runs the existing `Linter.lint_source`, then invokes
  `parse_module_silent_checked` and only afterward runs AST collection and other
  semantic checks (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:57-68,
  113-126`). This is not a cached compiler/HIR query path.
- Parse failure is correctly fail-closed: it emits deny-level `PARSE001`, records
  the first parser location/reason, skips all AST rules, and returns immediately
  (`entry_and_fixes.spl:70-111`). The outer CLI translates the internal
  NOT-LINTED marker into failure and emits an explicit summary
  (`src/app/io/cli_lint_commands.spl:197-204,223-241`).
- Repository measurements attribute about 99% of size-dependent lint time to
  `parse_module_silent_checked`, with all lint checks about 1%; the measured
  slope is linear but extremely high, roughly 0.19–0.20 seconds per line
  (`doc/08_tracking/bug/lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md:7-17`).
  Therefore first-wave performance rules must reuse the compiler/daemon's parsed
  and typed artifacts; optimizing lint walkers alone cannot address the dominant
  cost.

## Severity, suppression, and machine output

Observed lint severity is only `Allow | Warn | Deny`; categories contain no
performance or optimization-remark category
(`src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:8-18`). `LintDiag` carries
code, level, category, message, optional hint and optional easy fix, while
`LintRunResult` adds only file/line/column
(`src/compiler/90.tools/lint/_LintMain/config_and_model.spl:756-808`). Thus it
cannot represent confidence, symbolic cost, evidence tier, related spans,
hotness, suppression rationale, or a structured “missed optimization”.

Human output maps Deny to `error` and Warn to `warning`
(`config_and_model.spl:810-834`). JSONL output exposes only type, file, line,
column, level, code and message (`entry_and_fixes.spl:466-500`). Fix hints,
EasyFix replacements/confidence, category, profile, evidence, cost and uncertainty
are absent from diagnostic JSON. SIMD emits the same record shape but uses
`level:"info"` outside the core level model
(`src/app/io/cli_lint_commands.spl:206-220`). This split is the closest existing
remark mechanism, but it is ad hoc.

Configuration supports project `simple.sdn` and leading file attributes
`@allow`, `@warn`, `@deny`, with scanning ending at the first definition or
module value (`config_and_model.spl:508-577,590-600`). Suppression and promotion
depend on `map_lint_code_to_config_name`; unknown codes are always kept and retain
their original level (`config_and_model.spl:602-630`). Critically, that mapping
has no `COLL*` branch (`config_and_model.spl:634-730`), and `all_lint_names` has
no collection/performance group (`config_and_model.spl:122-166`). Consequently
COLL diagnostics cannot currently be selectively suppressed or configured by
file/project policy. `--deny-all` can still make warnings fail at counting time
(`entry_and_fixes.spl:479-487`), but it does not produce a structurally promoted
diagnostic.

## Existing collection rules and gaps

`CollectionLintWarning` is an untyped record with textual code and severity,
message, hint and function name (`src/compiler/35.semantics/lint/collection_patterns.spl:40-52`).
The textual severity is discarded by integration: COLL001/COLL006 are hardcoded
to Deny and all others to Warn (`entry_and_fixes.spl:125-145`). Locations are
recovered by textual line search because AST spans are absent on this path
(`entry_and_fixes.spl:132-145`), which cannot reliably distinguish multiple
findings of the same rule.

Implemented/reserved IDs:

| IDs | Observed state |
|---|---|
| COLL001 | array concat in loop; implemented, default Deny |
| COLL002 | array `contains` in loop; implemented, default Warn |
| COLL003 | `remove(0)` queue drain; implemented, default Warn |
| COLL004 | loop-invariant method call; implemented, default Warn |
| COLL005 | chained filters; implemented, default Warn |
| COLL006 | string concat in loop; implemented, default Deny |
| COLL007 | rebuild-to-pop; implemented, default Warn |
| COLL008 | unbounded global push; implemented, default Warn |
| COLL009–018 | deliberately reserved for CollectionPlan diagnostics (`collection_patterns.spl:15-17`), not implemented |
| COLL019 | mutation through indexed value-semantic access; implemented as a correctness rule (`collection_patterns.spl:13-17,80-83`) |

The planned IDs are: nested dynamic iteration, functional linear lookup,
repeated materialization, sequential indexing, repeated sort, unbounded flat-map,
accidental Cartesian product, missing index, complexity regression, and unknown
hot callback cost (`doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md:233-242`).
The current AST walker has no typed operation complexity, cardinality, effect,
alias, mutation, boundedness, hotness, or interprocedural summary. It therefore
cannot safely implement the reserved rules by extending string-pattern helpers.

CollectionPlan is currently a researched design, not an identified production
IR. Its proposed compilation sequence starts after HIR type/effect completion
and separates extraction, complexity, fusion, index selection, lowering and the
existing collection optimizer (`collection_plan_ir_2026-07-31.md:477-497`). Its
explicit compilation-cost contract is one cached AST/HIR traversal, cached
function summaries, bounded candidates and SCC propagation
(`collection_plan_ir_2026-07-31.md:545-557`). First-wave typed rules are already
prioritized as COLL009–012 and COLL018 (`collection_plan_ir_2026-07-31.md:584-586`).

## Recommended shared contracts

Introduce the requested anchors as canonical, typed contracts rather than
another warning struct:

- `PerfRuleId`: closed/stable identity for `COLL`, `LOOP`, `MEM`, and
  compiler-self-lint rules, with config group, default policy by profile,
  analysis tier, and diagnostic kind.
- `PerfDiagnostic`: location plus `PerfRuleId`, `DiagnosticKind` (`Warning`,
  `Error`, `RemarkPassed`, `RemarkMissed`, `RemarkAnalysis`), confidence,
  evidence tier, `CostExpr` before/after, memory delta, related spans, rejection
  reasons, and optional EasyFix. Project it into legacy `LintDiag` only at the
  CLI boundary.
- `OperationSummary`: typed time, allocation count/bytes, cardinality, effects,
  access/order/uniqueness and invalidation rules. It must be the shared registry
  consumed by lint, CollectionPlan, optimizer remarks, IDE and CI.
- `CostExpr`: bounded symbolic algebra with explicit `Unknown(reason)`, expected
  versus worst-case distinction, canonicalization and complexity caps. Never
  turn an unknown proof into a warning/error assertion.

Machine JSON should be versioned and include `kind`, stable rule ID, category,
effective severity, configured/default severity, profile, primary and related
spans, confidence, tier, symbolic work/allocation/cardinality, evidence, missed
reason, fix confidence/replacements, and suppression eligibility. Keep JSONL
stdout pure and retain current file/run summary records.

Suppressions should target stable `PerfRuleId` or groups (`performance`,
`complexity`, `allocation`, `remarks`), record a reason for deny-level overrides,
and never suppress analysis-incomplete or parse-failure certification failures.
Intentional Cartesian products and protocol-bounded loops need explicit bounded
facts/annotations, not broad file suppression.

## First-wave implementation boundaries

1. **Foundation only:** add `PerfRuleId`, `PerfDiagnostic`, `OperationSummary`,
   `CostExpr`, versioned rendering, performance category/group configuration,
   and exact-span transport. Do not change existing COLL severities yet.
2. **Parse reuse boundary:** expose a lint query over the compiler session's
   cached parse + typed HIR/MIR. Preserve standalone lint as a thin session owner;
   do not add a second performance parser or repository scanner.
3. **Tier-0, high-confidence warnings:** implement COLL009–012 plus MEM001
   allocation-in-dynamic-loop and repeated setup/materialization only when
   `OperationSummary` and typed receiver facts are known. Suppress fixed small
   bounds and emit no finding on `Unknown`.
4. **Remarks, not warnings:** unknown callback cost (COLL018), missed fusion,
   missed reserve, vectorization blockers and uncertain alias/effect cases.
   These must never affect normal exit status.
5. **Defer semantic substitutions:** COLL013–016 index/sort/Cartesian/flat-map
   transformations, general loop fusion, hash-index synthesis and public layout
   changes remain warning/remark-only until equality, order, effect, alias,
   cardinality and profitability proofs exist. The CollectionPlan research also
   gates Dict synthesis and lambda source fixes on runtime/backend prerequisites
   (`collection_plan_ir_2026-07-31.md:561-572`).
6. **CI-only boundary:** COLL017 complexity regression requires stable cached
   summaries and a baseline artifact; it is not an editor lint and must report
   analysis-incomplete rather than certify within exceeded budgets.

Acceptance for the first wave should prove: one parse per module/session; stable
human and versioned JSON semantics; config/suppression mapping for every new ID;
no warning for fixed-small or unknown-cost cases; exact primary spans; remarks do
not change exit status; and existing COLL001–008/019 diagnostics retain behavior
until separately migrated and baselined.
