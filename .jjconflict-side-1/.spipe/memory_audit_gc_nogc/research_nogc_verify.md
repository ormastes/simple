# Empirical Verification: Does "nogc" Mode Actually Avoid GC at Runtime?

Date: 2026-06-11. Read-only audit; test artifacts in `/tmp/nogc_verify/` (not in repo).

## VERDICT: nogc is naming-only at runtime (partial static lint only)

**There is no garbage collector in compiled Simple programs at all.** Both "gc" and
"nogc" code lower to the exact same runtime calls backed by plain libc
`malloc`/`calloc` via Rust's global allocator, and the compiler never emits a free or
collect. "GC mode" today mechanically means *allocate-and-leak*. So nogc trivially
"avoids GC" — but only because GC does not exist in the native output; the gc/nogc
split has **zero codegen or runtime effect** (byte-identical binaries, see §3).
Enforcement is a shallow, path-literal lint (warn/deny at `bin/simple lint` time only),
not a compile-time guarantee.

---

## 1. How the compiler decides gc vs nogc

### Self-hosted compiler (`src/compiler`, NOT the deployed compiler — `bin/simple` is the Rust seed)
- `src/compiler/00.common/gc_config.spl:1-60` — `GcMode {Gc, NoGc}`; hierarchy
  `simple.sdn` → directory `__init__.spl @no_gc` → file `@no_gc`. NoGc maps bare `T`
  to Unique pointer kind (design intent, lines 44-62).
- `src/compiler/99.loader/module_resolver/manifest.spl:167-184` — sets
  `GcConfig.from_module(GcMode.NoGc)` from `@no_gc`.
- `src/compiler/35.semantics/gc_boundary_check.spl:1-50` — cross-family import check;
  header says **"Produces warnings (not errors)"**. Contains
  `RUNTIME_FAMILY_MANIFEST` table (common=neutral rank 0 … gc_async_mut=gc rank 4).
- `src/compiler/35.semantics/noalloc_checker.spl:1-13` — `@noalloc` per-function pass,
  "hard errors": DirectAlloc / TransitiveCall / FamilyImport. Exported via
  `35.semantics/__init__.spl:104-118`.
- Caveat: the self-hosted compiler is not deployed (stage4 deploy blocked), so these
  passes do not govern what `bin/simple` does today.

### Rust seed (`src/compiler_rust`, the compiler that actually runs)
- Parser accepts `@no_gc` as a known attribute: `parser/src/parser_impl/attributes.rs:35`.
- **No semantic or codegen consumer of GcMode exists in the seed** — grep for
  `gc_mode|GcMode` in `compiler/src` (non-test) returns nothing.
- The only enforcement is a lint: `compiler/src/lint/checker_core.rs:405-406` calls
  `check_gc_boundary_imports`, implemented at
  `compiler/src/lint/checker_resources.rs:548-602`. Family detection:
  path `src/lib/<family>/…` (`checker_resources.rs:785-798`) or bare `@no_gc` line in
  first 30 lines (`checker_resources.rs:852-878`). Import family is matched **only on a
  literal path segment** equal to a family name (`runtime_family_from_import_segments`,
  `checker_resources.rs:800-809`). Default level: `LintLevel::Deny`
  (`lint/types.rs:212`).

## 2. Runtime allocation functions (GC vs non-GC)

- **There is one shared allocator for everything.** No Boehm, no rt_gc_alloc symbol
  exists anywhere.
- `src/runtime/runtime_memory.c:12-19` — `rt_alloc` = `calloc`, `rt_free` = `free`.
- `src/compiler_rust/runtime/src/value/collections.rs:184-194` —
  `alloc_runtime_string` = `std::alloc::alloc` (libc malloc);
  `rt_string_new` at `collections.rs:1409` uses it. Arrays/objects same pattern.
- `src/compiler_rust/runtime/src/value/heap.rs:45-72` — `HeapHeader` carries tri-color
  mark bits (`gc_flags::WHITE/GRAY/BLACK`)… **but no collector ever reads them in a
  compiled program.** `SHARED_ROOTS` registry
  (`runtime/src/memory/gc.rs:356-377`) has zero consumers outside one integration test
  (`test/integration/runtime_integration.rs:75-77`).
- Real tracing GC (`GcRuntime`, abfall crate, `runtime/src/memory/gc.rs:203-291`) exists
  only inside the **driver process**, and its `alloc_bytes` is called only from
  `compiler/src/smf_builder.rs:53` and `smf_writer.rs:56-58,169` — i.e. it tracks SMF
  artifact bytes, **not program values**. `--gc-off` selects `NoGcAllocator`
  (`runtime/src/memory/no_gc.rs:1-30` — a leak-forever `Vec<Box<[u8]>>`); selection at
  `driver/src/cli/basic.rs:12-19`.
- Refcount primitives exist (`rt_shared_new/clone/release`,
  `runtime/src/value/objects.rs:514-592` — release really frees at count 0;
  `rt_unique_free`, `rt_arena_alloc`) but are opt-in externs.

## 3. What each mode lowers to (codegen evidence)

- MIR `GcAlloc` → **Cranelift**: plain call to `rt_alloc` (= calloc) —
  `compiler/src/codegen/instr/memory.rs:163-175` (`compile_gc_alloc`), wired at
  `codegen/cranelift_emitter.rs:143-144`.
- MIR `GcAlloc` → **LLVM**: `build_alloca` stack slot named `"gc_alloc"` —
  `codegen/llvm/functions/memory.rs:78-88`. (A "GC allocation" becomes a stack alloca.)
- **No deallocation is ever emitted**: `rt_free`/`rt_unique_free`/`rt_shared_release`
  are merely registered as callable externs (`codegen/runtime_sffi.rs:442-473`); no MIR
  lowering emits Free/Drop (grep `MirInst::Free|emit_free` in `mir/lower` = empty).
- `mir/effects.rs:109-239` models a `GcAlloc` effect / `nogc_program()` predicate, but
  it feeds effect classification only, not allocator selection.

## 4. Empirical tests (commands run)

```
bin/simple compile /tmp/nogc_verify/gc_ver.spl    --native -o gc_ver_bin     # no attr
bin/simple compile /tmp/nogc_verify/nogc_bare.spl --native -o nogc_bare_bin  # bare @no_gc line
md5sum gc_ver_bin nogc_bare_bin
  -> 19285eb3642b8a81a93d47d96346e119  BOTH (byte-identical, 2,839,624 bytes)
```
- Program: string concat + `[i64]` push loop + prints. `@no_gc` (bare attribute form,
  the one the lint recognizes) produced a **byte-identical binary** → zero effect on
  native code generation.
- `nm -D <bin>`: only `malloc/calloc/free/realloc@GLIBC` — no GC library linked.
  `strings`: full `rt_*` extern surface (incl. `rt_shared_*`, `rt_unique_*`,
  `rt_arena_*`) but no collect entrypoint; binary auto-stripped.
- `bin/simple --gc-log run simple2.spl`: **zero GC log events** for a string/array
  workload (GcRuntime untouched by program values). `--gc-off` behaves identically.
- Enforcement tests:
  - `bin/simple lint violate3.spl` (bare `@no_gc` + `use std.gc_async_mut.gpu.{Device}`)
    → `error: runtime family 'nogc_sync_mut' must not import 'std.gc_async_mut.gpu'
    (nogc_imports_gc_family) [L:gc_boundary_crossing]`, exit 1. **Lint does catch the
    literal form.**
  - Same import via the real-world alias `use std.gpu` (which resolves into
    `gc_async_mut`) → `OK`, exit 0. Comment form `# @no_gc` → `OK` (not recognized).
  - `bin/simple compile violate3.spl --native` → **exit 0, compiles fine** (plus a
    `[CODEGEN-STUB-FALLBACK]` silently stubbing `gpu_global_size_z`). So the boundary
    is not enforced at compile/run time, only when you explicitly run `lint`.

## 5. What the specs actually verify

- `test/01_unit/compiler/semantics/gc_safety_spec.spl` — every `it` body is `pass`
  with assertions in comments. Verifies nothing.
- `gc_boundary_enforcement_spec.spl` — header admits it tests **replicated local
  helper copies** of the logic ("No imports: all logic is replicated at module level"),
  and that in interpreter mode `it` bodies don't even execute.
- `alloc_checker_spec.spl` — entire suite commented out; single `it "skipped"`.

## 6. Answers to the task questions

1. **Does nogc avoid GC allocation paths?** Vacuously yes: there are no GC allocation
   paths in compiled output. Strings/arrays/closures/objects in *every* tree go through
   the one shared malloc-backed runtime (`rt_string_new`/`rt_array_*` →
   `std::alloc::alloc`; `GcAlloc` → `rt_alloc`/alloca) and are never collected or freed.
2. **Is nogc enforced?** Conventional + one shallow lint. `gc_boundary_crossing`
   (Deny) fires only on literal `std.<family>.…` import segments from files under
   `src/lib/<family>/` or with a bare `@no_gc` line, and only when `lint` is run.
   Compile/run never check it. The self-hosted `noalloc_checker` (hard errors) and
   `gc_boundary_check` (warnings) are not in the deployed compiler path.
3. **gc_boundary_enforcement / alloc_checker mechanics:** import-direction rules over
   the `RUNTIME_FAMILY_MANIFEST` rank table (nogc must not import gc; noalloc must not
   import any allocating family); alloc_checker additionally classifies direct
   allocations and transitive allocating calls inside `@noalloc` fns — but its spec is
   skipped and the pass lives only in the un-deployed self-hosted compiler.

## 7. Bugs observed during verification

- **B1 (crash):** array-push loop *inside* `fn main` then `print(arr.len())` dumps core
  in both native (exit 139) and interpreter mode; the identical code at module level
  works. Repro: `/tmp/nogc_verify/b1.spl` vs `v1.spl`.
- **B2 (lint blind spots):** `# @no_gc` comment form (used in real docs/examples) is
  ignored by family detection (`checker_resources.rs:869-877` wants a bare line);
  aliased imports (`use std.gpu` → gc_async_mut) bypass the boundary lint entirely.
- **B3 (silent miscompile):** compiling a file importing `std.gc_async_mut.gpu` emits
  `[CODEGEN-STUB-FALLBACK] ... 'gpu_global_size_z': rt_gpu_num_groups not found` and
  replaces the function with an empty stub, still exiting 0.
- **B4 (dead machinery):** HeapHeader tri-color flags and the SHARED_ROOTS registry are
  written but never consumed by any collector — dead weight implying an unfinished GC.
