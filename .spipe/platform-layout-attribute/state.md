# SStack State: platform-layout-attribute

## User Request
> next task from the plan — platform_layout_attribute (7 phases: typed model, attribute syntax, matching, layout integration, diagnostics, tests, migration)

## Task Type
feature

## Refined Goal
> Implement platform layout attribute infrastructure: attribute parsing (@platform with key=value predicates), match filtering against compile target with specificity selection, layout variant integration for size/align/offset, diagnostic errors for missing @platform on ABI-facing types, and migration scaffolding.

## Acceptance Criteria
- [ ] AC-1: Platform attribute parser — parse @platform, @platform(bit), @platform(key=value) forms with validation
- [ ] AC-2: Attribute validation — reject unknown keys/values, reject duplicate predicates, reject duplicate defaults
- [ ] AC-3: Match filtering — filter platform variants against compile target descriptor
- [ ] AC-4: Specificity selection — select most-specific match, error on ambiguous equal-specificity
- [ ] AC-5: Default fallback — require at most one default, use it when no specific match
- [ ] AC-6: Layout variant integration — platform-selected size, alignment, field offset metadata
- [ ] AC-7: Pointer width from bit — @platform(bit) resolves to target pointer width (32/64)
- [ ] AC-8: Diagnostic: missing @platform — error on ABI-facing types with platform-varying layout but no @platform
- [ ] AC-9: Migration scaffolding — annotator helper for SFFI/HAL/OS structs needing @platform
- [ ] AC-10: Verification spec — 20 tests covering parsing, validation, matching, layout, diagnostics

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 7 plan phases. Existing: PlatformAbi, PlatformBit, PlatformPredicate, PlatformVariant in type_layout_part1.spl. Task: build attribute parsing, match filtering, layout integration, diagnostics, migration.

### 5-implement
<pending>
