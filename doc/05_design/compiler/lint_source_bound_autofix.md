# Source-bound warning fixes and described suppressions

Status: source candidate; compiler, native build, CLI and test execution UNRUN. The existing campaign execution budget remains exhausted. Source review does not establish all-warning-clean status.

## Actual existing routes

`app.cli.lint_entry` dispatches through `app.io.cli_lint_commands`. Lint reaches `compiler.tools.lint._LintMain.entry_and_fixes`; `app.lint.main` reexports this owner. `simple fix` reaches `compiler.tools.fix.main.FixToolApplicator`. The retained app.fix rule facade is not a new CLI implementation.

The lint writer previously flattened all replacements into one requested file, bypassed existing overlap checks, ignored replacement paths and coordinate consistency, and reread source after analysis without comparing revisions. The shared low-level applicator retains a permissive malformed-range fallback. The fix CLI checked overlap but lacked source-revision validation before disk writes.

## Admission through existing APIs

The new tools.fix.source_edits leaf validates every replacement path against the analyzed source map, half-open text-index ranges, one-based line/column coordinates, overlap and ambiguous same-position insertion. It then delegates to the established FixApplicator, so malformed input cannot reach its fallback. Both existing application routes use this leaf. Confidence policy is unchanged; Allow diagnostics are excluded even with --fix-all. No Any/type inference rewrite or unsafe marker is added.

Lint retains the actual source used for analysis and passes it into apply_collected_fixes. The trailing optional source argument preserves call syntax but calls without provenance now refuse action with an explanation. No existing production caller other than the owner route was found. Parse-failed files cannot apply collected edits. Disk content must equal the retained analyzed source before preview/write and immediately before a write. The fix CLI preflights every affected source before its first write, then rechecks each target.

These equality checks reject already-stale snapshots; file_atomic_write supplies existing atomic replacement behavior. They are not filesystem compare-and-swap and cannot eliminate a concurrent write after the final check. Multi-file writes are not an atomic transaction: a late race/write failure can leave prior files updated. No stronger concurrency claim is made.

## Intentional warnings

The existing file-header attribute parser now requires `@allow(named_rule) # reason: <description>`. Missing/empty reasons and blanket all/warnings/* requests emit located LINTALLOW001 and do not lower the rule. Existing @warn/@deny behavior is preserved. The parser reuses RawRtLexState in its existing incremental header walk, so normal/triple strings and comments cannot become suppression directives. Issues are carried in resolved configuration and rendered by the existing lint pipeline, without another source scan. This is file-level named-rule scope; no new statement/method suppression grammar is invented.

Warnings without machine-applicable fixes retain their specific diagnostic/hint and add guidance to prefer a safe idiom. An intentional warning needs a scoped description. Unsafe markers are appropriate only when the operation's actual contract requires them; the tool never inserts one to hide a warning. No reason text is synthesized.

## Evidence, costs and limits

The new SSpec invokes actual FixToolApplicator, apply_collected_fixes, Linter and LintConfig APIs, including the existing signature-proven RAW-RT-002 env_set producer. It tests exact edited text, unchanged stale files, malformed coordinates/conflicts, multi-file preflight, confidence, lexical exclusion, and retained underlying warnings. All scenarios are authored UNRUN; no CLI autofix or test run is claimed.

Validation uses one line-offset index per affected source and sorting per replacement group, O(source length + replacements log replacements), followed by the existing applicator's sort. State is request-local. File reads are limited to explicit preflight/recheck, not polling. No persistent cache or startup scanner is introduced; runtime cost/RSS remains unmeasured.

Only the four touched existing owner files were checked for existing @allow directives: zero. No signature-proven supported warning rewrite was confirmed in those owned files. Therefore this packet applies no fabricated cleanup or suppression to production source, and makes no all-warning-clean claim. Donor, staging, encoding and inference owners remain untouched; root owns review/application and future authorized verification.

Revision 2 reconciles existing `fix_atomic_write_failure_check.spl`: its directory target now fails source admission before any atomic write. The retained filename preserves callers, while comments/output accurately describe invalid-source rejection and directory preservation. This oracle does not exercise file_atomic_write failure. Actual atomic-write-failure coverage remains unqualified; no fake provider or permission assumption was introduced. Production implementation and 17 new scenarios are unchanged.

<!-- wave-f-perf-analysis-collection-refactoring-2026-11-19 -->

## Semantic legality obligations and `--fix-safe` lifecycle for collection refactors (2026-11-18)

Canonical plan: [Simple Performance Analysis and Collection Refactoring](../../03_plan/compiler/performance_analysis_and_collection_refactoring_2026-11-18.md) (`D06`, `D10`, §7, §10, §16.2; contracts in `src/compiler/35.semantics/perf/perf_analysis_contracts_v1.spl` and `src/lib/common/diagnostics/fix_transaction.spl`).

### Separation of recognition, legality, and profitability

Loop-to-collection and performance-related rewrites separate three questions (`D06`): (1) structural **recognition** (`LoopIdiomCandidateV1`), (2) language-semantic **legality** (`SafetyObligationStatusV1`), and (3) resource **profitability**. Passing tests or re-typechecking after an edit is regression evidence, never a substitute for discharging semantic preconditions (`D10`).

### 13-point `VerifiedSafe` proof obligations (`SafetyObligationKind`)

Automatic application (`PerfFixApplicability.VerifiedSafe` / `FixApplicability.Automatic`) requires every one of the 13 obligations in `perf_analysis_contracts_v1.spl` to be discharged:

1. `collection_identity` — replacing a fresh local builder cannot alter an object identity or partial buffer observable elsewhere (`S06`).
2. `aliasing` — input collections, output builders, captured references, and iterators do not alias or interfere (`S03`).
3. `mutation` — callbacks neither mutate the iterated source nor depend on partially built output prefixes (`S04`).
4. `evaluation_order` — exact callback/iterator call count, order, and short-circuit termination (`any`/`all`/`find`) are preserved (`S12`).
5. `timing_eagerness` — eager loops keep an eager terminal consumer (`collect()` / `fold(...)`) at the exact original point (`S02`).
6. `failure_prefix_cleanup` — mid-iteration error order, visible prefix state, fallback evaluation, and scope cleanup/destructors match (`S05`, `S18`).
7. `control_flow_exits` — `break`, `continue`, labeled exits, and early `return` paths are modeled and preserved.
8. `capture_lifetime` — value/reference capture bindings, ownership, and borrow lifetimes remain valid.
9. `numeric_semantics` — fold seeds on empty inputs (`S07`), non-associative order (`S08`), floating-point rounding/NaN/signed-zero order (`S09`), and checked overflow traps (`S10`) are preserved.
10. `output_shape_duplicates` — result type, duplicate-key retention, grouped vs flat join shape (`S16`, `S17`), and empty-input results match.
11. `runtime_effects` — I/O, volatile/MMIO, locks, clocks, RNG, async suspension, and cancellation points are never reordered or dropped (`S11`).
12. `resource_restrictions` — active `nogc`, fixed-capacity, and declared `@cost` memory/allocation limits are respected (§10.4).
13. `revision_currency` — source bytes (`source_hash`), document `version`, `expected_text`, callee effect summaries, and library model versions (`dependency_fingerprint`) match the current snapshot (`I01`, `I02`).

Any unknown or unmet obligation downgrades the candidate to `Unavailable` (`PERF-FIX-001`) or `ReviewRequired` (for index/join/allocation tradeoffs). LLM-generated or solver-synthesized patches never self-assign `VerifiedSafe` (§10.1).

### 8-stage safe edit lifecycle and `--fix-safe` batch rules

1. **Discover** candidates read-only without touching disk or overlay buffers.
2. **Resolve** lazily against the exact source and typed HIR revision when requested.
3. **Validate** all 13 obligations plus `EditTransaction` triple preconditions (`version`, `source_hash`, `expected_text`) and `dependency_fingerprint`.
4. **Preview** minimal syntax-preserving diffs (preserving comments, indentation, captures, and unexpanded macro boundaries, `S15`) alongside honest cost/allocation tradeoff notes (`S14`).
5. **Apply** deterministically through `EditTransaction`, rejecting overlapping or conflicting spans (`OverlappingEdits`, `I07`).
6. **Check** by reparsing/type-checking and running selected verification specs.
7. **Record** rule ID, before/after digests, discharged assumptions, and verification status.
8. **Recover** cleanly without overwriting concurrent user edits if validation fails.

In `--fix-safe` batch mode, dependent semantic facts are recomputed between chained edits so invalidated candidates are skipped rather than applied stale, rewrite cycles are bounded, `ReviewRequired` algorithm changes (`PERF-ALG-001`) are excluded with an explanation, and `@allow(...)` suppressions are never synthesized automatically (§10.3).
