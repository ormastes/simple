# Seed HIR: method on a `T?` receiver typed by a shorter-named owner -> `struct 'Void' field 'ready'`

- **Filed:** 2026-11-04 (jitvoid lane, follow-up 1 of PR #6627)
- **Status:** FIXED in seed source (2026-11-04); seed redeploy is the bootstrap lane's.
- **Platform:** any (HIR lowering); found on aarch64-apple-darwin.

## Symptom

`simple run test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl`
printed `[jit-fallback] HIR lowering error: Cannot infer field type: struct 'Void'
field 'ready'` and dropped the whole module to the interpreter. The failing
expression is NOT in the spec: it is co-compiled from
`src/lib/gc_async_mut/gpu/engine3d/engine.spl` `Engine3D.end_frame()`:

```simple
val active = self._vulkan_font          # VulkanFontAdapter3D?
if active != nil:
    var vulkan = active.?               # HIR type stays Pointer{inner: VulkanFontAdapter3D}
    val evidence = vulkan.end_frame()   # typed as Engine3D.end_frame() -> void
    ... evidence.ready ...              # struct 'Void' field 'ready'
```

## Root cause

`lookup_method_return_type_inner` (`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`)
looked up `Owner.method` only for `Struct`/`Enum` receivers. `opt.?` keeps the
flat-nullable `Pointer { inner: T }` type (`lower_exists_check`), so the lookup
fell through to the `.method` suffix search, whose shortest-owner-name tiebreak
picked `Engine3D.end_frame` (void) over `VulkanFontAdapter3D.end_frame`.
`.ready` then failed because `ready` is declared on several structs.

Minimal repro (needs: a shorter-named owner of a same-named void method, and an
ambiguous field name): see `compiler/tests/jit_nullable_receiver_method_return_type.rs`.

## Fix

Peel `Pointer { inner: Struct|Enum }` to `inner` before the `Owner.method`
lookup. Evidence (seed built from the worktree):

| check | before | after |
|---|---|---|
| `cargo test --test jit_nullable_receiver_method_return_type` | FAIL (HIR lower error) | PASS |
| `native_gpu_font_readback_spec.spl` `simple run` | `jit-fallback` HIR error | no HIR error; then `jit-bail:no-main-fn` (spec files have no `main`, so the runner interprets them — separate, by design) |
| Engine2D collector of that spec wrapped in a `main` (std.spec import removed), `SIMPLE_JIT_STRICT=1 simple run` | — | JIT ran: `engine2d status=pass target=vulkan nonblank=true cpu_oracle_parity=true readback_bytes=16384` |
| spec `simple run` totals | 5/8 | 5/8 (unchanged: Engine3D `public-vulkan-font-install-failed`, missing SimpleOS QEMU `evidence.env`, latency/budget example) |
| `cargo test -p simple-compiler --lib` | 23 failing | same 23 (pre-existing, identical set) |

Remaining gap: keeping `std.spec` in the probe hits a separate JIT closure-ABI
refusal (`function 'skip' creates a lambda/closure the JIT closure ABI cannot
compile`), so a spec file itself still cannot run on the JIT.
