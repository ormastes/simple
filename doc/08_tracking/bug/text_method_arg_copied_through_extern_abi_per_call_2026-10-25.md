# `content.index_of(...)` copies `content` through the extern text ABI per call (2026-10-25)

Status: OPEN. bug_db.sdn: DB reconciliation pending. Source workaround on
work/p3fix-g2lineend (`_driver_line_end`). Compiler root fix not written.

## Symptom
Phase 3 gen-1 (S/r27/g2/simple.g1c, sha 0326cbeb; same on bp/simple.probe24) uses
>90G in `phase1:load_sources:closure` before parse: run-28g2 attempts b-e and every
probe were cgroup-OOM-killed (90G/105G). Single-process probe (PSH=0, entry of 1094
modules): RSS 1G -> 58.7G in ~40 s while loading `compiler.hir.generated.hir_codec`
(316,778 bytes). Stack samples (SIGSEGV sent to the worker at 3G and 8G, shim
S/r27/g2/shim/bt.so): `rt_string_new_uncached_impl` <- `_driver_line_end+0x90` <-
`_driver_entry_import_module_paths_text_fallback` <- `_driver_entry_import_module_paths`
<- `_driver_cached_entry_source_scan` <- `_driver_collect_explicit_compiler_source`.

`_driver_line_end` (run-27e Stage-2 object) lowers `content.index_of("\n", start)` as
`rt_interp_cstr(content)` + `rt_string_len` + `rt_string_new` (a full copy of
`content`, plus one of the literal) and only then `rt_text_find`. Called once per
line, it copies the whole file per line: O(bytes x lines) transient allocation,
released only at scope end. Same extern-text-ABI-copy family as B11 (bug doc
transient_promote_text_promotes_abi_copy_2026-10-25, on branch work/p3fix-p3b4 7f0ba55dcb5, not yet on main).

## Repro (Stage 2; untracked src/app/zz_g2lineend in worktree simple-p3fix-g2lineend)
1.17 MB text, 20,000 lines, one call per line:
- a (natural `index_of("\n", start) ?? -1`): `a lines=20000`, maxrss 22.9 GB, 9.27 s.
- b (`byte_at` scan, the workaround): `b lines=20000`, maxrss 7.8 MB, 0.02 s.

## Workaround
`src/compiler/80.driver/driver_source_loading.spl` `_driver_line_end`: forward
`byte_at` scan for byte 10, same result contract (index of the next newline at or after
`start`, else `content.len()`). Tagged
`@workaround bug=text_method_arg_copied_through_extern_abi_per_call_2026-10-25`.
`byte_at` lowers to the direct `__simple_rt_string_byte_at` (no copy) in this binary.

## Remaining sites (same family, bounded)
The caller `_driver_entry_import_module_paths_text_fallback` still calls
`content.index_of("\"\"\"", ...)` per docstring-bearing line and `contains()` three times;
those are not per-line over every line and were not the measured hog. The compiler
root fix (no ABI copy for text method receivers) retires all of them.

## Spec
`test/01_unit/compiler/driver/driver_line_end_spec.spl`.
