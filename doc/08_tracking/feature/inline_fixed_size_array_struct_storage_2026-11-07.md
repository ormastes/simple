# FR-LANG-INLINE-FIXED-ARRAY-0001 — inline fixed-size `[T; N]` struct storage

**Filed:** 2026-11-07 (owner-approved re-scope)
**Status:** request
**Priority:** P2
**Split from:** `doc/08_tracking/bug/noalloc_collections_backed_by_growable_heap_array_2026-08-07.md`

## Request

Add a language-level fixed-size array type `[T; N]` (N a compile-time
constant) that can be embedded directly as a struct field, with its storage
laid out inline in the enclosing struct (or static/stack slot) and **no heap
allocation** at construction or at any later point.

## Why

`nogc_async_mut_noalloc/collections/*` (`FixedArray`, `FixedStack`,
`FixedMap`) are now allocation-free *after construction*, but their backing
storage is still a heap `[T]` filled once in `new()`. True noalloc
(static/inline storage, required by the WP-12 allocation-class lattice) is not
expressible today because the language has no inline fixed-size array.

## Acceptance

- `struct S: buf: [i64; 16]` compiles; `sizeof(S)` includes the 16 elements.
- Constructing/using `S` performs zero heap allocations (measured, not by doc comment).
- Index bounds checked against `N`; out-of-range is a compile error when constant.
- The noalloc collections migrate to `[T; N]` storage, closing the remaining
  inline-storage scope of the linked bug.
