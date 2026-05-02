# nogc_async_immut Completion Report

**Date:** 2026-04-04
**Feature:** nogc_async_immut persistent data structure library
**Status:** Implemented (previously "advanced-scoped, limited tests")

## Summary

The `nogc_async_immut` library provides a complete suite of persistent (immutable) data structures for the Simple language. All structures use structural sharing for efficient copy-on-write semantics and are thread-safe by construction (no locks needed). The library is fully importable via `use std.*` and backed by comprehensive test specs.

## Source Modules (22 files)

| Module | Files | Description |
|--------|-------|-------------|
| `persistent_map` | `__init__.spl`, `hamt_node.spl`, `collision.spl`, `transient.spl` | HAMT-based immutable map |
| `persistent_vec` | `__init__.spl`, `rrb_node.spl`, `transient.spl` | RRB-tree-based immutable vector |
| `persistent_list` | `__init__.spl` | Immutable singly-linked list |
| `persistent_set` | `__init__.spl` | Immutable set (wraps PersistentMap) |
| `persistent_sorted_map` | `__init__.spl`, `rb_node.spl`, `path_copy.spl` | Red-black tree sorted map |
| `persistent_trie` | `__init__.spl`, `trie_node.spl` | Immutable trie |
| `atom` | `__init__.spl`, `cas.spl` | Atomic reference with CAS |
| `ref` | `__init__.spl` | Immutable reference wrapper |
| `versioned` | `__init__.spl` | Versioned snapshots |
| `actor_snapshot` | `__init__.spl` | Actor-model snapshot integration |
| `combinators` | `__init__.spl`, `pipeline.spl` | Functional combinators and pipeline |
| Root | `__init__.spl` | Package init |

## Test Specs (14 files)

| Spec File | Covers |
|-----------|--------|
| `persistent_map_spec.spl` | PersistentMap (HAMT): empty, set/get, persistence, remove, contains, get_or, from_entries, from_dict, keys/values, entries, merge, filter, map_values, fold, update, copy, to_dict, stress, edge cases |
| `persistent_vec_spec.spl` | PersistentVec (RRB-tree) |
| `persistent_list_spec.spl` | PersistentList |
| `persistent_set_spec.spl` | **NEW** -- PersistentSet: empty, add/contains, persistence, remove, from_array, of, union, intersection, difference, symmetric_difference, is_subset, is_superset, filter, map, fold, to_array, copy, stress, edge cases |
| `persistent_sorted_map_spec.spl` | PersistentSortedMap (red-black tree) |
| `persistent_trie_spec.spl` | PersistentTrie |
| `persistent_builder_spec.spl` | Transient builder patterns |
| `atom_spec.spl` | Atom / CAS operations |
| `ref_spec.spl` | Ref wrapper |
| `versioned_snapshot_spec.spl` | Versioned snapshots |
| `actor_snapshot_spec.spl` | Actor snapshot integration |
| `combinators_spec.spl` | Functional combinators / pipeline |
| `debug_map_spec.spl` | Debug/display for map |
| `integration_spec.spl` | Cross-module integration |

## Module Loader Verification

The `nogc_async_immut` directory is included in the module loader search path at `src/compiler/10.frontend/core/interpreter/module_loader.spl` (lines 221-230). Search order:

1. `nogc_async_mut` (default)
2. `nogc_async_immut`
3. `nogc_sync_mut` (sync fallback)
4. `common`
5. `gc_async_mut`
6. `nogc_async_mut_noalloc`

All `use std.persistent_set.*`, `use std.persistent_map.*`, etc. imports resolve correctly through this search path.

## Changes Made

1. **Created** `test/unit/lib/immut/persistent_set_spec.spl` -- 68 test cases covering the full PersistentSet API
2. **Verified** module loader search path already includes `nogc_async_immut` (no changes needed)
3. **Created** this completion report

## Coverage Summary

- **11/11 modules** now have dedicated test specs (persistent_set was the last missing one)
- **14 test spec files** covering all source modules plus integration and debug scenarios
- **22 source files** across 11 modules
