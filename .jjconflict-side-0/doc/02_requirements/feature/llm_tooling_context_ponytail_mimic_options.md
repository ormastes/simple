# Requirement Options: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## Option A: Context Pack First

Implement the existing `simple context` generator/stats functions.

Requirements:

- `context_generate(path, target, format)` returns non-empty markdown, text, and
  JSON for readable files.
- `context_stats(path, target)` returns line and token estimates.
- Output is nil-free.
- No new raw runtime shortcuts outside existing CLI owner helpers.

Pros:

- Smallest useful replacement step.
- Reuses existing CLI and tests.
- Unlocks later index/search and ponytail review work.

Cons:

- Does not yet provide persistent search/indexing.
- Does not yet replace context-mode fetch/index tools.

Effort: Small.

## Option B: Context Pack + Local Index

Implement context pack generation plus a local append-only index under
`.build/context/`.

Requirements:

- Everything in Option A.
- Store labeled packs with source, timestamp, and compact content.
- Add a query command over stored packs.

Pros:

- Closer to context-mode behavior.
- Enables dashboard and review workflows sooner.

Cons:

- More file format and invalidation decisions.
- Higher risk of ad hoc search implementation.

Effort: Medium.

## Option C: Full Context/Ponytail Tool Suite

Build context generation, local indexing, query, dashboard panels, and ponytail
simplification reports in one lane.

Pros:

- Most complete replacement story.

Cons:

- Too broad for one safe slice.
- Higher chance of speculative abstractions.
- Harder to verify and review.

Effort: Large.

## Recommended Selection

Option A. It is the first rung that holds: existing CLI surface, smallest
working replacement, and enough behavior to support later index/review slices.

