# Segment-granular loader: wiring verification and fix — 2026-08-18

Scope: `startup_perf_architecture_2026-08-17.md` §8.4 (one mapping per
segment, not per symbol) and §8.15 (loader performance targets).

## 1. Is the segment mapper wired in, or dead code?

**Wired in.** `src/compiler/99.loader/module_loader_compat.spl`'s SMF load
branch (`ModuleLoader.load`, the `Ok(reader)` arm) was already rewritten
(uncommitted diff present at session start) to:

- collect distinct `section_index` values from exported symbols,
- call `SegmentMapper.map_segment` once per distinct section (not once per
  symbol),
- call `SegmentMapper.bind_symbol` per symbol (pure offset arithmetic, no
  allocation),
- scope relocation RX↔RW flips to `begin_relocation`/`end_relocation` per
  section instead of per symbol,
- build a `LoadPlanV1`/`LoadReceiptV1` pair via `segment_load_plan` /
  `segment_load_receipt` and store the check result on
  `ModuleLoader.last_load_segment_count` / `last_load_plan_ok` etc.

The old per-symbol path (`native_alloc_exec_memory` inside a per-symbol
loop) is **gone from this branch** — confirmed by re-reading the diff
against `module_loader_compat.spl` and grepping for `native_alloc_exec_memory`
in that file: it now appears only in the `use` line (which this session
trimmed to the functions actually called: `native_reloc_write_i32`,
`native_reloc_write_i64`, `native_call_function_0`).

A separate, still-live per-symbol path exists in
`src/compiler/99.loader/loader/object_mapper.spl` /
`src/compiler/99.loader/object_mapper.spl` (`map_symbol`), used by the JIT
instantiation lane (`jit_instantiator.spl`, `module_loader.spl`,
`generation_sweeper.spl`) for individually-JIT-compiled functions. That is a
different, legitimate use case (§8.14, per-function JIT, not a whole-module
static SMF load) and is out of scope for §8.4.

## 2. Bug found and fixed: the mapper never actually executed mapped code

`SegmentMapper` (`segment_mapper.spl`) and `module_loader_compat.spl` both
resolve `compiler.loader.smf_mmap_native` to
`src/compiler/99.loader/smf_mmap_native.spl` (top-level file; the
similarly-named `src/compiler/99.loader/loader/smf_mmap_native.spl` is a
**different** module, `compiler.loader.loader.smf_mmap_native`, used only by
`object_mapper.spl`).

That top-level file's `native_alloc_exec_memory` / `native_write_exec_memory`
/ `native_make_executable` / `native_make_rw` were a **Dict-backed
simulation** (`_g_fake_next_addr`, `_g_fake_memory`) despite the file's own
header comment claiming to "replace the old stub that returned 0/false for
everything." `native_call_function_0` unconditionally returned `0`. Address
arithmetic in `SegmentMapper` was correct (proven by the passing
`segment_mapping_count_spec.spl` and 7 of 8 examples in
`segment_symbol_resolution_spec.spl`), but nothing mapped was ever real
executable memory, so calling through a resolved address could never
succeed.

Fix applied to `src/compiler/99.loader/smf_mmap_native.spl`:
- `native_alloc_exec_memory` / `native_alloc_rw_memory` / `native_free_exec_memory`
  now call the real `rt_mmap_raw`/`rt_munmap_raw` SFFI (same externs the
  file already declared but never used for these paths).
- `native_write_exec_memory` and `native_mmap_read_bytes` now use the
  `rt_ptr_write_u8`/`rt_ptr_read_u8` extern wrappers.
- `native_make_executable` / `native_make_rw` now call real `rt_mprotect`.
- `native_reloc_write_i32` / `native_reloc_write_i64` now call real
  `rt_ptr_write_i32`/`rt_ptr_write_i64` instead of writing into the fake Dict
  — this matters because `module_loader_compat.spl`'s relocation loop calls
  these directly against `seg_base` (a mapper-returned address).

**Dead end tried and reverted:** an `unsafe: (addr) as *u8` / `fn_ptr as fn()
-> i64` cast-based implementation (mirroring the sibling
`loader/smf_mmap_native.spl`) was tried first. It fails to *compile* under
the current bootstrap-seed interpreter with `semantic: type mismatch:
unsupported cast target type: Pointer { kind: Shared, inner: Simple("u8") }`
— a whole-file compile error, which is why the first rerun showed 6/8
examples failing (up from 1/8) instead of getting closer to green. Reverted
to the extern-call form, which is the same one already proven to work under
`bin/simple test` by `test/01_unit/compiler/loader/native_mmap_byte_read_spec.spl`.

## 3. What is still red, and why it is an engine gap, not a mapper bug

`test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl`, describe
"POSITIVE CONTROL: the mapped code still executes correctly", `it "calls
each symbol and gets that symbol's own value back"` — **still fails**
(`assert_equal failed: expected 33, got 0`) after the fix above, under
`bin/simple test`. 7 of 8 examples in that file pass, including both address
placement examples and all bounds/lifecycle examples.

Root cause: **there is no supported mechanism to invoke an arbitrary `i64`
code address as a function from Simple running on this interpreter.**
- `fn_ptr as fn() -> i64` is rejected at compile time with the same
  "unsupported cast target type: Pointer" error as above.
- There is no `rt_call_*`-style C runtime extern for an unknown-arity raw
  function-pointer call (checked `src/runtime/*.c`).
- This is a pre-existing, already-documented limitation elsewhere in the
  tree: `test/02_integration/app/loader_exec_memory_spec.spl` explicitly
  works around it with local stub re-definitions and the comment "skip:
  native exec memory functions require compiled mode (not interpreter)".

`native_call_function_0` in `smf_mmap_native.spl` is left returning `0`
with a comment explaining why, rather than a broken cast that fails the
whole file. Per the "never weaken a spec" rule, the POSITIVE CONTROL
assertion itself is **not** touched — it stays red, and correctly documents
that real execution cannot yet be proven under this engine. This should be
tracked as a `doc/08_tracking/bug/` item if the project wants "real
execution provable under `bin/simple test`" as a hard requirement; that
would need either interpreter support for raw function-pointer calls or a
new `rt_call_i64_i64` (or similar fixed-arity) C runtime extern plus SFFI
wiring — a materially larger change than this task's scope, so it was not
attempted.

## 4. Files touched this session

- `src/compiler/99.loader/module_loader_compat.spl` — trimmed a now-unused
  `use` clause left over from the segment-mapper rewrite (no behavior
  change).
- `src/compiler/99.loader/smf_mmap_native.spl` — replaced the Dict-simulated
  alloc/write/protect/relocate paths with real `rt_mmap_raw`/`rt_mprotect`/
  `rt_ptr_write_*` SFFI calls; left `native_call_function_0` returning 0
  with an explanatory comment (engine gap, see §3).

No test files were modified. `segment_mapping_count_spec.spl` and
`segment_symbol_resolution_spec.spl` were re-run (not edited) to verify.

## Verification log

- Binary used for all verdicts: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
  59645008 bytes, mtime `2026-08-18 10:12:23 UTC` — identical before and
  after every run in this session (stamped via `readlink -f bin/simple` +
  `stat`).
- `segment_symbol_resolution_spec.spl`: before this session's edits, 7/8
  passed (per coordinator report). After the reverted cast attempt: 6/8
  failed (whole-file compile error). After the extern-based fix: back to
  7/8 passed, same single genuine failure (POSITIVE CONTROL, engine gap).
- `segment_mapping_count_spec.spl`: re-run after the native-layer fix to
  confirm the mapping-count claim is unaffected by switching from fake to
  real memory.
