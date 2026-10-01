# Bootstrap LLVM signature lookup repeatedly scans the full function table

- **Date:** 2026-08-16
- **Component:** pure-Simple flat MIR-to-LLVM bootstrap emission
- **Severity:** medium (bootstrap compile-time scalability)
- **Status:** FIXED 2026-09-06 (scan removed); acceptance item 4 NOT satisfiable
  on the fixing host — see "Fix, 2026-09-06" below.
- **Correctness owner:** `MirToLlvm.bootstrap_llvm_function_index_for_name`
- **Perf owner (new):** `bootstrap_llvm_exact_function_index` /
  `bootstrap_llvm_module_local_function_index` in
  `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`

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

## Fix, 2026-09-06

### Precondition found first: the scanning method was not in the tree

`bootstrap_llvm_function_index_for_name` landed in `a5b334cbc98` (2026-08-16,
the day this record was filed) and was **deleted two days later by
`cb1e4981701`** ("refactor(backend): reroute backend_api wildcards — SCC 24 ->
8"). That commit is a stale-snapshot clobber of the anti-revert shape described
in `.claude/rules/vcs.md`: -150/+45 on
`_MirToLlvm/core_codegen.spl`, of which only the `use
compiler.backend.backend_api.*` removal and its three
`rt_enum_discriminant`/`rt_tuple_get` rewrites are explained by the title. It
also dropped, unexplained and unrelated to the wildcard: this lookup method and
all four of its call sites, `first_unemitted_call_destination`, the
discriminant-based `Call` dispatch with its emitted-destination panic, the
`defined_locals` emission receipt, and the float-to-`ptr` return-mismatch panic.
**Only the signature lookup is repaired here** — the other four are a separate
correctness regression and are NOT in scope of this record.

With the method gone, the four queries fell back to the receiver dictionaries
`register_bootstrap_signatures` populates, which is the very
`Dict<text, ...>` shape the "Required fix" above forbids as the owner.

### What changed

- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` — new immutable flat
  scalar index, owned by that module and NOT by the long-lived `MirToLlvm`
  receiver: sorted parallel `[i64]` arrays (`_bootstrap_llvm_exact_key_*`,
  `_bootstrap_llvm_base_key_*`) plus `bootstrap_llvm_exact_function_index` and
  `bootstrap_llvm_module_local_function_index`. Ordering is by a bounded integer
  digest, never by `text` `<` (native codegen resolves that as a raw POINTER
  compare, so a text-ordered table would not be reproducible); a probe is a
  binary search plus a walk of one equal-digest run where exact `text` equality
  decides. Rebuild is keyed on `(epoch, count)`, the epoch bumped by
  `bootstrap_mir_functions_reset`. Nothing but i64 row indices crosses back — no
  `MirType`, no per-function array, no dictionary.
- `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` — restored
  `me bootstrap_llvm_function_index_for_name`, now a thin orchestrator over
  those two owners, keeping the original ordering (exact first, then the
  runtime-owned exclusion, then the module-local basename branch). Restored the
  four fallbacks in `lookup_function_return_unsigned`,
  `lookup_function_return_type`, `lookup_function_param_type` and
  `lookup_function_param_count`.
- `test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl`
  — new behavioural `it`, "resolves bootstrap signature names through the flat
  scalar index without scanning the table".

`register_bootstrap_signatures` is deliberately left alone: it is a single
O(n) pre-pass, not a per-query scan, and removing it is a separate behavioural
change (its last-writer-wins duplicate handling differs from the index's
fail-closed one).

### Measurement (acceptance item 2)

Both sides measured in ONE process, one tree, one binary, over the REAL
accumulators — 10,460 stub functions loaded through `bootstrap_mir_functions_add`,
2,000 exact queries (75% hits, 25% `rt_*` misses). Baseline is the deleted
method's own loop replayed over the same `bootstrap_mir_function_*_at`
accessors. Harness:
`/tmp/.../scratchpad/measure_index.spl` (scratch, not committed).

| | rows scanned | query wall | index build |
|---|---|---|---|
| full-table scan per query | 20,920,000 | 177,726 ms | — |
| flat sorted scalar index | 1,500 | 314 ms | 2,980 ms (one-off) |

Hit counts identical (1,500/1,500). Rows scanned per query is now the length of
one equal-digest run — 1 on this fixture — so total scanned rows is bounded by
`signature_lookups`, not by `function_count x signature_lookups`: 13,947x fewer
rows, 566x faster on queries, 54x faster including the one-off build.

### Invariants verified

By the new spec, against the real owner: exact-name resolution; unknown name ->
-1; emitted `main` (both `main` and `__simple_main` reach the same row, and a
second provider literally spelled `__simple_main` makes that spelling
ambiguous); duplicate canonical providers -> -1; module-scoped basename
uniqueness (`f` resolves per module, is -1 in a module with two providers, and
-1 for `module_index < 0`); reset invalidation. Runtime-owned exclusion and the
`@` prefix strip stay in the receiver method, byte-identical to the
pre-deletion source. Access is scalar throughout.

### Not satisfied, stated plainly

- **Acceptance item 4 (no Rust-seed evidence) is NOT met.** The fixing host
  (aarch64) has no runnable pure-Simple binary: `bin/simple` resolves to the
  Rust seed and says so, `bin/simple_native` is an x86-64 ELF, and the tracked
  stage binaries SEGV (see
  `stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`). Every
  number and every spec result above was produced by the seed. The counted-rows
  result is implementation-independent, the wall times are not.
- **Acceptance items 1 and 3 (Stage 3 admission; wall time and max RSS on the
  full compiler closure with warm caches) are NOT measured** — a full bootstrap
  was out of budget on a box already running one.
- Five `it` blocks in the spec file above were **already red before this
  change** and remain red: they assert source text of the wider
  receiver-ownership refactor that `cb1e4981701` clobbered
  (`emit_bootstrap_signatures_statics_and_functions`, the receiver-construction
  shape in `driver_bootstrap.spl`, the string-globals move, the call-conversion
  diagnostics). Restoring those is the separate correctness regression named
  above. `test/01_unit/compiler/bootstrap/bootstrap_runtime_name_collision_order_spec.spl`
  is red for a related reason and additionally asserts an ordering (runtime
  guard BEFORE the exact scan) that no shipped implementation ever had — the
  version this fix preserves puts the exact resolution first.

### Runnable check

```
bin/simple run test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl
```

Expect `✓ resolves bootstrap signature names through the flat scalar index
without scanning the table` alongside the five pre-existing failures above
(`6 examples, 5 failures`).
