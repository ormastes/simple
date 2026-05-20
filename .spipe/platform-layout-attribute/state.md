# SStack State: platform-layout-attribute

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — platform_layout_attribute (7 phases: typed model, attribute syntax, matching, layout integration, diagnostics, tests, migration)

## Task Type
feature

## Refined Goal
> Implement platform layout attribute infrastructure: attribute parsing (@platform with key=value predicates), match filtering against compile target with specificity selection, layout variant integration for size/align/offset, diagnostic errors for missing @platform on ABI-facing types, and migration scaffolding.

## Acceptance Criteria
- [x] AC-1: Platform attribute parser — parse @platform, @platform(bit), @platform(key=value) forms with validation
- [x] AC-2: Attribute validation — reject unknown keys/values, reject duplicate predicates, reject duplicate defaults
- [x] AC-3: Match filtering — filter platform variants against compile target descriptor
- [x] AC-4: Specificity selection — select most-specific match, error on ambiguous equal-specificity
- [x] AC-5: Default fallback — require at most one default, use it when no specific match
- [x] AC-6: Layout variant integration — platform-selected size, alignment, field offset metadata
- [x] AC-7: Pointer width from bit — @platform(bit) resolves to target pointer width (32/64)
- [x] AC-8: Diagnostic: missing @platform — error on ABI-facing types with platform-varying layout but no @platform
- [x] AC-9: Migration scaffolding — annotator helper for SFFI/HAL/OS structs needing @platform
- [x] AC-10: Verification spec — 20 tests covering parsing, validation, matching, layout, diagnostics

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 7 plan phases. Existing: PlatformAbi, PlatformBit, PlatformPredicate, PlatformVariant in type_layout_part1.spl. Task: build attribute parsing, match filtering, layout integration, diagnostics, migration.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/compiler/30.types/platform_attr_parser.spl — PlatformAttrKey + PlatformAttrValue + PlatformAttrForm + AttrValidationResult
- src/compiler/30.types/platform_match.spl — CompileTarget + PlatformPredMatch + VariantMatch + MatchSelector + MatchResult
- src/compiler/30.types/platform_layout_variant.spl — PointerWidth + FieldLayout + PlatformLayoutVariant + PlatformLayoutSelector
- src/compiler/30.types/platform_diagnostic.spl — PlatformDiagnostic + TypePlatformCheck + MigrationCandidate + MigrationReport
- test/unit/compiler/platform_layout_attr_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
