# Custom Primitive SFFI and Public API Requirement Options

Date: 2026-04-20

## Option A: SFFI-Only Transparent Newtypes

Support custom primitive wrappers only in SFFI exported classes and function signatures.

Pros:

- Smallest useful compiler change.
- Directly fixes SFFI raw primitive pressure.
- Lower regression risk for SimpleOS and HAL.

Cons:

- Bitfields still need separate work.
- Public primitive API migration remains manual and inconsistent.
- Backend behavior may still diverge outside SFFI paths.

Effort: Medium.

## Option B: Compiler-Wide Custom Primitive Resolver

Add a shared resolver for named transparent primitive wrappers and use it in SFFI lint, FFI generation, backend C/LLVM type mapping, bitfield width resolution, and primitive API lint/audit.

Pros:

- Fixes the root cause instead of individual call sites.
- Supports SFFI custom primitives and SFFI bitfields together.
- Gives OS/HAL/SFFI migrations a consistent rule.
- Enables better diagnostics: convertible, blocked, or exempt.

Cons:

- Touches more compiler phases.
- Requires focused ABI and layout regression tests.
- Needs careful staging to avoid changing generated C signatures unexpectedly.

Effort: Large.

## Option C: Public API Lint and Migration Plan Only

Improve `primitive_api` lint to suggest domain wrappers and produce an audit report, but do not change ABI lowering yet.

Pros:

- Fastest path to inventory and cleanup guidance.
- Low compiler backend risk.
- Useful even if ABI support is delayed.

Cons:

- Does not satisfy SFFI custom primitive usage.
- Does not make bitfields accept custom primitive types.
- Risks papering over places that still cannot compile or interoperate.

Effort: Small to Medium.

## Option D: Full API Migration in One Pass

Add custom primitive ABI support and immediately convert all SimpleOS, HAL, and SFFI public primitive APIs.

Pros:

- Maximum semantic cleanup.
- Best long-term API surface if successful.

Cons:

- Highest blast radius.
- Hard to review and bisect.
- Likely to expose unrelated Simple language, bitfield, SFFI, and backend bugs at the same time.

Effort: Extra Large.

## Recommendation

Select Option B for implementation, followed by staged API migrations from the audit report. Do not choose Option D as the first implementation slice.
