# Platform Layout Attribute Plan

Date: 2026-04-20

## Phase 1: Typed Platform Model

- Consolidate or bridge existing `TargetArch`, SMF `Platform`, and target text helpers.
- Add `PlatformAbi`, `PlatformBit`, and `PlatformPredicate`.
- Normalize parser strings to enums during semantic lowering.

## Phase 2: Attribute Syntax

- Parse:
  - `@platform`
  - `@platform(bit)`
  - `@platform(default, bit=64)`
  - `@platform(cpu=x86_64, os=linux, abi=gnu, bit=64)`
- Reject unknown keys and values.
- Reject duplicate exact predicates except that duplicate defaults are also errors.

## Phase 3: Matching Semantics

- Implement match filtering against compile target.
- Select most-specific matching variant.
- Error on ambiguous equal-specificity matches with different layout effects.
- Require at most one default fallback.

## Phase 4: Layout Integration

- Extend `LayoutAttr` or adjacent metadata with platform variants.
- Teach `type_layout.spl` to use the selected platform variant for size, align, and field offset checks.
- Make `@platform(bit)` use target pointer width.

## Phase 5: Diagnostics

- Error when an ABI-facing struct/class/custom primitive has platform-varying size or offsets but lacks `@platform`.
- Error when a field has platform-varying layout and neither the field nor enclosing type is tagged.
- Warn when `@platform` appears on layout-affecting declarations without explicit `bit`, `size`, or `align`.

## Phase 6: Tests

- Parser tests for accepted syntax and rejected duplicates.
- Semantic tests for unknown enum values.
- Layout tests for 32-bit vs 64-bit target selection.
- SFFI/HAL tests for missing `@platform` errors.
- Ambiguous-match tests proving no order-dependent first/last matching.

## Phase 7: Migration

- Annotate platform-sensitive SFFI, HAL, and OS structs.
- Keep exact wire/on-disk structs fixed-size unless they intentionally vary by target.
- Integrate with custom primitive resolver so platform-sized primitive wrappers require explicit `@platform`.
