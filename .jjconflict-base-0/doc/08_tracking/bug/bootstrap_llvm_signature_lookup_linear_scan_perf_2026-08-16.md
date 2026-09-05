# Bootstrap LLVM signature lookup repeatedly scans the full function table

- **Date:** 2026-08-16
- **Component:** pure-Simple flat MIR-to-LLVM bootstrap emission
- **Severity:** medium (bootstrap compile-time scalability)
- **Status:** OPEN / TODO
- **Correctness owner:** `MirToLlvm.bootstrap_llvm_function_index_for_name`

## Problem

The correctness repair for staged receiver corruption removed the retained
whole-program signature dictionaries from `MirToLlvm`. The replacement keeps
signature authority in immutable scalar bootstrap tables, but
`bootstrap_llvm_function_index_for_name` scans `bootstrap_mir_function_count()`
to the end for every exact lookup and can perform a second full scan for a
module-local basename.

The current Stage 3 inventory contains about 10,460 functions. Return-type,
parameter-type, and parameter-count queries all call this lookup from emitted
call sites. The retained upper bound is therefore
`O(function_count * signature_lookups)` and can approach quadratic behavior as
the compiler closure grows. The previous receiver dictionaries are falsified
as a safe remedy and must not be restored: their long-lived mutable
whole-program state was the corruption risk this fallback removed.

## Required fix

Build an immutable flat scalar index outside the long-lived `MirToLlvm`
receiver, preserving:

- exact-name uniqueness and duplicate fail-closed behavior;
- emitted `main` name handling;
- runtime-owned name exclusion;
- module-scoped basename uniqueness;
- scalar type-tag access without transporting `MirType` or per-function arrays
  on the receiver.

A sorted parallel name/module/index table with binary-search ranges, or an
equivalent staged-native-safe scalar owner, is acceptable. A receiver-owned
whole-tree `Dict<text, ...>` is not.

## Acceptance evidence

On the same frozen Stage 2 compiler/runtime/source identity:

1. Stage 3 remains admitted with exact and ambiguous-name fixtures green.
2. Instrumented lookup work is bounded sublinearly per query (or a build-time
   counter proves total scanned rows is not proportional to
   `function_count * signature_lookups`).
3. Wall time and max RSS are compared on the full compiler closure with warm
   caches preserved.
4. No Rust-seed result is accepted as behavioral or performance evidence.

This TODO is intentionally not part of the Stage 3 conversion-blocker fix; it
records the retained performance debt so a correctness fallback is not
mistaken for a scalable final design.
