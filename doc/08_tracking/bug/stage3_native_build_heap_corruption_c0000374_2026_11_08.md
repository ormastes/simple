# Pure-Simple stage3 native-build heap corruption (c0000374), even on hello world

Status: OPEN. Found 2026-11-08 while retesting
phase2_result_payload_native_crash_2026_10_26.

Binary: `C:/dev/p3new/s3new/s3_fable64b.exe` (24498176 bytes, built 2026-11-08 12:02,
contains the MIRV-001n guard strings), Windows x64.

## Repro (exact)

```
printf 'fn main() -> i64:\n    print "hi"\n    0\n' > hello.spl
C:/dev/p3new/s3new/s3_fable64b.exe native-build hello.spl -o hello.exe   # exit 139
```
Same exit 139 with and without SIMPLE_PARSE_SHARD_MAX=1 SIMPLE_MIR_SHARD_COUNT=1
SIMPLE_NATIVE_BUILD_THREADS=1. Also 139 for
test/fixtures/compiler/phase2_result_byte_codec/{result_payload,direct_payload_control}.spl.
Log ends right after `[frontend-cache] hits=1 misses=0 parses=0`.

## Evidence
`lldb -b -o run -- s3_fable64b.exe native-build ...` prints
`Critical error detected c0000374` (STATUS_HEAP_CORRUPTION); stop is inside
ntdll (LdrResSearchResource + 2037, int3 fail-fast), no compiler frame.
No PDB/map exists under C:/dev/p3new/s3new (only symbol lists fable*_syms.txt).
PageHeap not attempted: `gflags` (Windows SDK debugging tools) is not installed.

## Consequence
The direct control (which passed on the earlier admitted Phase2 compiler) also
fails here, so this failure is NOT specific to Result payloads; it blocks
verifying phase2_result_payload_native_crash_2026_10_26 on this binary.

## Next
Install gflags/PageHeap or build stage3 with symbols; catch first bad write.

## Root cause (2026-11-09)

Status: fix-implemented-verification-pending (PR #7872).

Isolation: a cold HIR cache (`SIMPLE_HIR_CACHE_DIR` pointing at an EMPTY dir)
crashes identically, so no on-disk entry is involved. lldb breakpoints on
`rt_transient_array_scope_begin/pause/end` with `HeapValidate` show the heap
valid on entry to the HIR-cache scope's `rt_transient_array_scope_end`; the
crash is the next `malloc` (debug-heap free-fill check, which `HeapValidate`
does not cover). `finish` on `hir_cache_load_in_owned_scope` returned
`0x...3be1`: an `RtCoreEnum` (kind 4) with `transient_scope_id = 2`, i.e. the
`None` box of `HirModule?` (`HirModule` is a struct, so native `nil` is a
heap-boxed enum), allocated INSIDE the decode scope. `hir_cache_load` then
ended the scope (freeing the box) and returned the dangling pointer:
`hir_cache_load_parsed_v1`'s `loaded == nil` read freed memory (false),
`.unwrap()` + `module.path = source_path` wrote into it, and the driver took
the hit branch (`capture_native_parsed_objectless_v1` ran on a miss) until
`rt_string_new` in `module_source_relative_path` tripped c0000374.

Why the s3sanity runner "works": `C:/dev/wt/imphist_run.ps1` sets
`SIMPLE_HIR_CACHE=0` (hir_cache_load returns before the scope begins), ignores
native-build's exit code, and relinks the cached objects manually.

Fix: `hir_cache_load` (src/compiler/80.driver/driver_hir_cache.spl) decides
hit-ness while the box is still live (inside the paused scope) and returns a
fresh `nil` after `transient_scope_end`. Sweep: it is the only
`transient_scope_begin` site in 80.driver whose function returns an Option.

Red/green (native, s3_fable64b.exe lane from the repo root with
`SIMPLE_HIR_CACHE=0 --runtime-bundle core-c-bootstrap`, manual relink
`@<exe>.link.rsp -lwinhttp`):
- `test/fixtures/compiler/transient_scope_option_struct_nil/escaping_nil_red.spl`
  (old shape): `miss-case hit=true`, exit 1.
- `test/fixtures/compiler/transient_scope_option_struct_nil/scoped_nil_green.spl`
  (fixed shape): `miss-case hit=false`, `hit-case hit=true`, exit 0.
End-to-end (hello world builds on a stage3 built from this fix) is pending a
stage3 rebuild.

## Found alongside (not fixed here)
- General class: `Option<struct>` `nil` is a heap-boxed `None` in native code,
  so any `nil` created inside a transient scope and returned past its end is
  dangling. Only hir_cache_load does this today; a runtime/codegen-level
  immediate `None` would remove the class.
- `SIMPLE_HIR_CACHE=0 native-build hello.spl` from a non-repo cwd dies with
  c0000005 in `compiler.backend.runtime_compiler._runtime_dir_not_found_message`
  -> `spl_str_concat` (runtime dir lookup failure path crashes instead of
  reporting).
- Default runtime bundle link line lacks `-lwinhttp` on x86_64-pc-windows-gnu
  (`WinHttp*` undefined); `core-c-bootstrap` also lacks it; the runner's manual
  relink is the workaround.
- `rt_transient_heap_scope_selfcheck` / `rt_transient_promote_share_selfcheck`
  compile and PASS on Windows (llvm-mingw) when linked by hand; the capsule
  script refuses `MINGW64_NT` hosts.
