# Driver registers ~6,359 duplicate/alias SourceFiles (1.6x the source list)

**Date:** 2026-07-31
**Status:** OPEN — measured, not yet fixed
**Found while:** investigating the stage-3 whole-tree parse-state defect. It is
**not** the cause of that defect (see "Not the discriminator" below), but it is a
real defect on its own.

## Measurement

Driving the real resolver helpers in
`src/compiler/80.driver/driver_source_loading.spl`
(`_driver_collect_sources`, `_driver_resolve_entry_import`,
`_driver_collect_entry_import_source`) and replicating the closure-walker at
`driver_source_pipeline_loading.spl:163-254`, over
`--source src/compiler --source src/lib --source src/app`:

| quantity | value |
|---|---|
| files on disk | 10,560 |
| `SourceFile` entries after the closure walk | **16,919** |
| duplicate / alias registrations | **+6,359 (~1.6x)** |

## Mechanism

`src/compiler/backend` is a symlink to `70.backend`, and imports use mixed
spellings. A single file can be registered under up to three distinct
`(path, module_name)` keys:

1. **canonical** — `compiler.70.backend.backend.vulkan_backend`
2. **same-path alias** — resolved via
   `_driver_resolve_numbered_compiler_import`'s last unconditional fallback
   (`driver_source_loading.spl:670`, `"compiler.backend"→"compiler/70.backend/backend"`).
   Same path as (1), but the computed `module_name` doesn't match the import
   string, so it is pushed as an alias rather than deduped. Comes from
   one-segment imports like `codegen_factory.spl:18`.
3. **symlink-exact** — `compiler.backend.backend.vulkan_backend`, resolved
   through the symlink by `_driver_try_entry_import_rel`
   (`driver_source_loading.spl:528-540`). Lexically different path string, same
   inode. Comes from two-segment imports like `mir_test_builder.spl:37`.

Dedup is by `(path, module_name)`, and all three keys differ, so nothing
collapses. The `compiler.backend[.backend].X` mixed-spelling pattern has **223**
occurrences tree-wide. Note there is **no** canonical `compiler.70.backend.`
spelling anywhere in the source — every import into that tree goes through the
symlink.

## Not the discriminator for the stage-3 parse failure

Registration counts were compared for the file that fails to parse and a control
with the identical import pattern:

- `vulkan_backend.spl` (the victim): **3** registrations
- `codegen_types.spl` (control): **3** registrations

Both are 3, so duplicate registration does **not** explain why `vulkan_backend.spl`
specifically corrupts the parser while the rest of the `70.backend/backend/`
subsystem does not. Hypothesis rejected. Still open for that defect:
order/timing dependence, or a content-specific parser side-table interaction
(matches unresolved hypothesis 3 in the earlier vhdl bug doc).

## Why it is worth fixing anyway

INFERRED (not measured): a 1.6x inflated source list costs parse time and peak
memory on the whole-tree bootstrap — the exact build currently too slow/heavy to
complete under load on this machine. Deduping by canonical path (resolve
symlinks and re-derive `module_name` before the dedup key) could materially
reduce stage-3 cost. This should be measured, not assumed, once a bootstrap can
be run to completion.

MEASURED facts above (file counts, entry counts, per-file registration counts)
came from a throwaway `.spl` probe compiled with `native-build --entry-closure`
(164 files, ~62s) — deliberately cheap, versus a full-tree build that twice ran
1800s and 3600s without emitting a byte.
