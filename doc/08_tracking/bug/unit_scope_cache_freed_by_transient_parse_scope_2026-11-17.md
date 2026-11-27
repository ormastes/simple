# Unit-suffix lookup caches freed by the transient parse scope (Stage 2 SEGV / bogus "unit suffix 'u64' is not in scope")

- **Date:** 2026-11-17
- **Status:** fixed in source; native confirmation pending the next Stage 2 build
- **Area:** `src/compiler/10.frontend/core/unit_scope.spl`
- **Introduced by:** the 2026-11-17 unit-scope series (`cfc417914aa`, `8adc6bcaa75`, PR #9989), which added process-global lookup caches.

## Symptom

Stage 2 (integ7, `b0bc26617cf3`, aarch64) `native-build --entry-closure`, both backends:

- SEGV (exit 139) in the parse phase, last progress line `current=src/lib/common/crypto/sha256.spl`
  (fixture `test/fixtures/native_process_run_tuple_abi`).
- On smaller closures, no crash but a parse error on every file after the first:
  `parse error in m1.spl: 0:0:unit suffix 'u64' is not in scope; add  (or declare `unit X: T as u64`)`
  — note the empty hint list after `add`.

`sha256.spl` is a victim, not the cause: it is byte-identical to the previous
tip and is simply a file with many `0u64` / `0u8` literals.

gdb:

```
#0 compiler.frontend.core.unit_scope.unit_library_families
#1 compiler.frontend.core.unit_scope.unit_suffix_scope_error
#2 compiler__frontend___FlatAstBridge__convert_nodes__convert_flat_expr     (EXPR_SUFFIXED_LIT)
...
#8 ...module_assembly__parse_and_build_module_with_scope_owner
#9 ...module_assembly__parse_and_build_module_in_borrowed_scope
```

The faulting instruction is the inlined element load of the
`for org_dir in unit_library_orgs()` loop: the array's data pointer is garbage.

## Root cause

Every suffixed literal (`convert_nodes.spl` `EXPR_SUFFIXED_LIT`, including the
builtin `u8`/`u64`/`i32` ones) calls `unit_suffix_scope_error`, which consults
three module globals in `unit_scope.spl`: `unit_org_dirs`,
`unit_family_cache_sfx`, `unit_family_cache_fam`. They were filled lazily and
kept for the whole process.

The native driver parses each file inside a transient array scope
(`rt_transient_array_scope_begin` .. `_end`); scope end `free()`s every array
and text born inside it that was not explicitly promoted. The caches are born
while parsing the first file with a suffixed literal, so from the next file on
all three globals point at freed memory. Depending on heap reuse the read
returns stale-but-intact data (works by luck), a non-empty garbage `joined`
text (bogus "not in scope" error with no hints), or a wild data pointer (SEGV).

The seed interpreter is unaffected: its arrays are Rust values, not transient
scope allocations.

## Fix

The caches are now scope-lifetime instead of process-lifetime. Two bool flags
(`unit_org_dirs_loaded`, `unit_family_cache_loaded`) are the only state that
outlives a scope; `unit_library_cache_drop()` clears them in
`unit_scope_reset_from` (start of each file / interpreter run),
`unit_scope_restore` (end of each flat-bridge file) and
`unit_library_set_base`. The arrays are re-created on first use and never read
after a drop. Cost: one `dir_list` of the unit root plus one `file_exists` per
(distinct suffix, family) per file.

Promotion (`rt_transient_heap_promote`) was not used: it only works while the
scope is paused, and the caches are mutated on any later file, so they would
need re-promotion from every scope owner.

## No source workaround

There is no minimal workaround in `sha256.spl`: any file with a suffixed
literal parsed after another such file hits the freed cache. The current
integ7 Stage 2 binary needs a rebuild from a tree carrying this fix.

## Separate finding: fixture seed run rc=1

`check_fx.sh` runs `seed-tip-20261115/simple`, which predates the
`unit X: T` (no `as`) declaration form and fails on the current tree with
`src/lib/common/types.spl: Unexpected token: expected As, found Newline at line 23, column 19`.
The integ7 tree's own seed runs the fixture correctly (rc=0, 9 lines). This is
a stale harness seed, not a source defect.

## Evidence

- Spec `test/01_unit/compiler/frontend/unit_scope_cache_lifetime_spec.spl`:
  0/2 without the fix, 2/2 with it (integ7 seed).
- Native fixture `test/fixtures/native_suffix_literal_multi_file/`: the integ7
  Stage 2 fails it with the bogus parse error above (rc=1); the seed prints
  `total=27` / `b=1 3 c=6 9`. Must be re-run on the next Stage 2.
