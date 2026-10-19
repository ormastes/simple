# Source-bound warning autofix specification

Executable: `test/01_unit/compiler/lint/source_bound_autofix_spec.spl`.
Requirement: REQ-LINT-SOURCE-BOUND-FIX.
Status: 17 authored scenarios, all UNRUN. This is an authored manual, not generated execution evidence.

The actual public applicator must edit an admitted literal, reject foreign paths, negative/reversed/out-of-range spans, coordinate mismatches, overlap and same-point insertions, and preserve adjacent edits after a Unicode prefix. File-backed oracles assert stale lint source is unchanged, dry-run is read-only, pinned application writes expected bytes, missing provenance refuses, and a stale second simple-fix target prevents the first write. Confidence/Allow filtering remains explicit. A real RAW-RT-002 producer supplies an in-scope env_set rename to the same validated applicator; the fixture function is not executed.

Actual Linter/LintConfig scenarios require a located LINTALLOW001 plus the underlying warning for an undescribed @allow; a described named allow suppresses only its selected rule. Empty reasons and blanket scopes refuse. Comments/triple strings remain inert, and @warn/@deny do not need suppression descriptions.

No test runner, compiler, CLI autofix or native build was launched. No supported owned-source rewrite was verified outside these authored API fixtures, and the full warning census remains unqualified. The source guards do not claim a filesystem compare-and-swap transaction or atomic multi-file commit.

Revision 2 reconciles existing `fix_atomic_write_failure_check.spl`: its directory target now fails source admission before any atomic write. The retained filename preserves callers, while comments/output accurately describe invalid-source rejection and directory preservation. This oracle does not exercise file_atomic_write failure. Actual atomic-write-failure coverage remains unqualified; no fake provider or permission assumption was introduced. Production implementation and 17 new scenarios are unchanged.
