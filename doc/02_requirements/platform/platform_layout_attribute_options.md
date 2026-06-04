# Platform Layout Attribute Requirement Options

Date: 2026-04-20

## Option A: Marker and Diagnostics Only

Implement `@platform` as a marker for ABI-sensitive declarations and add warnings/errors for missing tags.

Pros:

- Smallest implementation.
- Immediately improves SFFI/HAL diagnostics.

Cons:

- Does not model per-target variants.
- Still leaves platform dimensions stringly or ad hoc.

Effort: Medium.

## Option B: Typed Platform Layout Variants

Implement typed platform dimensions, variant matching, default fallback, diagnostics, and target-aware layout selection.

Pros:

- Solves the root ABI-layout problem.
- Avoids first/last-match ordering mistakes.
- Composes with custom primitives, SFFI, HAL, and OS structs.

Cons:

- Requires parser, HIR, layout, and lint changes.
- Needs cross-target tests.

Effort: Large.

## Option C: General `@cfg` / Conditional Compilation

Use or extend `@cfg`/`@when` for platform layout and do not add a dedicated `@platform` attribute.

Pros:

- Fewer language features.
- Familiar to users who know Rust-style conditional compilation.

Cons:

- Too broad for ABI layout.
- Harder to enforce "platform-varying field must be tagged."
- More likely to hide untested layout paths.

Effort: Medium to Large.

## Recommendation

Choose Option B. Keep `@platform` narrow: layout/ABI facts only. General conditional code should stay with `@when`/`@cfg`.
