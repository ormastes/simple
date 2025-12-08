# Feature: Unique Pointers (#25)

**Memory/Pointer Feature**
- **Importance**: 4/5
- **Difficulty**: 4/5
- **Status**: COMPLETED

## Goal

Introduce a manual memory domain that mirrors the language's `&T` unique pointer: move-only ownership, deterministic drop, and explicit lifecycle tracking separate from the GC-managed default.

## Implementation

- Added `simple_common::manual::{ManualGc, Unique}` as the low-level contract for unique pointers.
- `ManualGc` tracks outstanding allocations (`live`/`collect`) for leak checks; `Unique` enforces move-only semantics, supports safe deref/mutation, and exposes `into_inner`/`is_valid` helpers.
- Strengthened GC coverage with a trait-level allocator test to validate the `GcAllocator` contract remains usable alongside manual pointers.

## Testing

- New unit tests in `src/common/tests/manual_unique.rs` cover drop tracking, `into_inner` consumption, and standalone unique mutation.
- Added `src/runtime/tests/gc_allocator.rs` to assert `GcRuntime` satisfies the `GcAllocator` trait surface.

## Notes

- Shared/weak/handle pointer kinds remain todo; the manual module is structured so those wrappers can piggyback on the same tracker infrastructure when added.
