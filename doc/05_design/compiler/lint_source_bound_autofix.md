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
