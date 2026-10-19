# Seed resolves `use X.*` / `use X.{...}` to `X/__init__.spl` when `X.spl` also exists

**Status:** OPEN — one instance removed (`src/compiler/50.mir/mir/__init__.spl`, 386762657a9); 43 pairs remain
**Filed:** 2026-10-19
**Severity:** P1 — silently loads a different module than the self-hosted compiler does; the symptom is a late "unknown static method" / missing impl, never a resolution error

## What happens

`prefer_package_init_for_member_import`
(`src/compiler_rust/compiler/src/pipeline/module_loader.rs:25`) rewrites a
resolved `<name>.spl` to `<name>/__init__.spl` when the import target is a
`Glob` or a `Group` and that package marker exists. A plain
`use X.Member` keeps `X.spl`. So under the seed the SAME module path loads
two different files depending on import syntax:

| import | seed loads | self-hosted driver loads |
|---|---|---|
| `use compiler.mir.mir.MirLowering` | `50.mir/mir.spl` | `50.mir/mir.spl` |
| `use compiler.mir.mir.*` | `50.mir/mir/__init__.spl` | `50.mir/mir.spl` |

The self-hosted driver (`src/compiler/80.driver/driver_source_loading.spl:1032`)
and the interpreter resolver
(`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:149`)
both try `<name>.spl` FIRST and `<name>/__init__.spl` only when it is absent,
for every import form. The seed rule inverts that order for two of the forms.

## Measured instance

`src/compiler/50.mir/mir/__init__.spl` (a 5-line ghost-erasure re-export with
zero consumers) shadowed `src/compiler/50.mir/mir.spl` for the 178 files that
`use compiler.mir.mir.*`. `mir.spl`'s `use ... mir_lowering` never ran, so the
`MirLowering` class reached the registry through other imports without
`module_lowering.spl`'s impl: `unknown static method new_for_target on class
MirLowering` in every spec that reaches it only via the facade.
`test/01_unit/compiler/mir/enum_match_fallthrough_trap_spec.spl` 0/6 → 6/6 after
deleting the marker. Stage 2/3 were never affected: no bootstrap list, SMF
manifest or baseline row names that file, and the self-hosted order already
picked `mir.spl`.

## Decision

The seed rule is the bug. Canonical order is the self-hosted one: `<name>.spl`
wins; `<name>/__init__.spl` is a package marker consulted only when no sibling
file exists. The `foo.spl + foo/__init__.spl` pair is itself the ambiguity the
resolver contract forbids (`src/compiler_rust/compiler/src/module_resolver/mod.rs:11`),
so the end state is zero pairs — but each pair needs a consumer audit first
(which file do its importers actually depend on under each toolchain?).
**Do not mass-delete.** `use_target_resolves_baseline.txt` and the
`check-guard-wiring` ratchet count filename mentions, so each removal is its own
reviewed change.

## Remaining pairs (44 measured 2026-10-19 in `src/`, one since removed)

- `src/app/cli/dispatch.spl + src/app/cli/dispatch/__init__.spl`
- `src/compiler/10.frontend/treesitter.spl + src/compiler/10.frontend/treesitter/__init__.spl`
- `src/compiler/15.blocks/blocks.spl + src/compiler/15.blocks/blocks/__init__.spl`
- `src/compiler/20.hir/hir_lowering.spl + src/compiler/20.hir/hir_lowering/__init__.spl`
- `src/compiler/30.types/type_infer.spl + src/compiler/30.types/type_infer/__init__.spl`
- `src/compiler/35.semantics/semantics.spl + src/compiler/35.semantics/semantics/__init__.spl`
- `src/compiler/70.backend/backend.spl + src/compiler/70.backend/backend/__init__.spl`
- `src/compiler/85.mdsoc/construct_types.spl + src/compiler/85.mdsoc/construct_types/__init__.spl`
- `src/compiler/85.mdsoc/types.spl + src/compiler/85.mdsoc/types/__init__.spl`
- `src/compiler_rust/lib/std/src/spec/matchers.spl + src/compiler_rust/lib/std/src/spec/matchers/__init__.spl`
- `src/compiler_rust/lib/std/src/sys.spl + src/compiler_rust/lib/std/src/sys/__init__.spl`
- `src/lib/common/math.spl + src/lib/common/math/__init__.spl`
- `src/lib/gc_async_mut/cuda.spl + src/lib/gc_async_mut/cuda/__init__.spl`
- `src/lib/gc_async_mut/gpu.spl + src/lib/gc_async_mut/gpu/__init__.spl`
- `src/lib/gc_async_mut/io.spl + src/lib/gc_async_mut/io/__init__.spl`
- `src/lib/gc_async_mut/net.spl + src/lib/gc_async_mut/net/__init__.spl`
- `src/lib/gc_async_mut/platform.spl + src/lib/gc_async_mut/platform/__init__.spl`
- `src/lib/gc_async_mut/spec.spl + src/lib/gc_async_mut/spec/__init__.spl`
- `src/lib/gc_async_mut/src/tensor.spl + src/lib/gc_async_mut/src/tensor/__init__.spl`
- `src/lib/gc_sync_mut/io.spl + src/lib/gc_sync_mut/io/__init__.spl`
- `src/lib/gc_sync_mut/net.spl + src/lib/gc_sync_mut/net/__init__.spl`
- `src/lib/gc_sync_mut/platform.spl + src/lib/gc_sync_mut/platform/__init__.spl`
- `src/lib/gc_sync_mut/spec.spl + src/lib/gc_sync_mut/spec/__init__.spl`
- `src/lib/gc_sync_mut/src/tensor.spl + src/lib/gc_sync_mut/src/tensor/__init__.spl`
- `src/lib/nogc_async_mut/async.spl + src/lib/nogc_async_mut/async/__init__.spl`
- `src/lib/nogc_async_mut/async_host.spl + src/lib/nogc_async_mut/async_host/__init__.spl`
- `src/lib/nogc_async_mut/concurrent.spl + src/lib/nogc_async_mut/concurrent/__init__.spl`
- `src/lib/nogc_async_mut/database/test_extended.spl + src/lib/nogc_async_mut/database/test_extended/__init__.spl`
- `src/lib/nogc_async_mut/fs.spl + src/lib/nogc_async_mut/fs/__init__.spl`
- `src/lib/nogc_async_mut/io.spl + src/lib/nogc_async_mut/io/__init__.spl`
- `src/lib/nogc_async_mut/net.spl + src/lib/nogc_async_mut/net/__init__.spl`
- `src/lib/nogc_async_mut/platform.spl + src/lib/nogc_async_mut/platform/__init__.spl`
- `src/lib/nogc_async_mut/spec.spl + src/lib/nogc_async_mut/spec/__init__.spl`
- `src/lib/nogc_async_mut/src/tensor.spl + src/lib/nogc_async_mut/src/tensor/__init__.spl`
- `src/lib/nogc_sync_mut/database/test_extended.spl + src/lib/nogc_sync_mut/database/test_extended/__init__.spl`
- `src/lib/nogc_sync_mut/debug.spl + src/lib/nogc_sync_mut/debug/__init__.spl`
- `src/lib/nogc_sync_mut/fs.spl + src/lib/nogc_sync_mut/fs/__init__.spl`
- `src/lib/nogc_sync_mut/io.spl + src/lib/nogc_sync_mut/io/__init__.spl`
- `src/lib/nogc_sync_mut/net.spl + src/lib/nogc_sync_mut/net/__init__.spl`
- `src/lib/nogc_sync_mut/platform.spl + src/lib/nogc_sync_mut/platform/__init__.spl`
- `src/lib/nogc_sync_mut/spec.spl + src/lib/nogc_sync_mut/spec/__init__.spl`
- `src/lib/nogc_sync_mut/spipe.spl + src/lib/nogc_sync_mut/spipe/__init__.spl`
- `src/lib/nogc_sync_mut/src/tensor.spl + src/lib/nogc_sync_mut/src/tensor/__init__.spl`
- `src/lib/nogc_sync_mut/tooling/easy_fix.spl + src/lib/nogc_sync_mut/tooling/easy_fix/__init__.spl`

## Fix options

1. Align the seed: drop `prefer_package_init_for_member_import` so Glob/Group
   resolve like a plain member import (`<name>.spl` first). Requires a seed
   rebuild + redeploy; the 43 pairs must be audited for files whose glob
   importers currently rely on the `__init__.spl` exports under the seed.
2. Until then, resolve pairs one at a time, as 386762657a9 did, with a
   zero-consumer proof for the losing file.
