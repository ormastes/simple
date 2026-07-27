# Stage 4 HIR Import Crash

## Status

OPEN. The pure-Simple Stage 3 compiler clears the prior address-of parser
failure, then segfaults during full-CLI HIR import resolution.

## Evidence

The focused Stage 4 run parsed
`src/compiler/mir/_MirLoweringExpr/expr_dispatch.spl` successfully, entered HIR
lowering, and stopped at:

```text
phase3:hir:file:start src/std/nogc_sync_mut/io/env_ops.spl
resolve_import_symbols:start module=src/std/nogc_sync_mut/io/env_ops.spl
```

Kernel evidence reports a null dereference at `0x5031f2`. `addr2line` and
disassembly map that address to `HirLowering.lower_trait`, where the generated
code dereferences its `Trait` argument. The leading hypothesis is the
`register_imported_symbol` path: its generated code calls `rt_enum_payload`
for `as_trait.unwrap()` immediately before calling `lower_trait`. No retained
core/backtrace proves that this caller supplied the null argument.

- Stage 2 SHA-256:
  `51c072812d5cd4b5b80ca2ff289d4e13d3a830adf679e58d61da6762066f816f`
- Stage 3 SHA-256:
  `c2a638a51df632e27352543a458289e857c16bfefd79e020bcce39c608f6870a`
- Strict run peak RSS: 2,549,240 KiB
- Focused Stage 4 peak RSS: 2,976,672 KiB
- Focused log:
  `build/bootstrap/cosmos-production-20260727/stage4-focused.log`

The strict wrapper did not reach Stage 4 because a tracked documentation edit
changed the dirty-state fingerprint during provenance measurement. Stage 2 and
Stage 3 had already passed sanity.

## Required Fix

Retain a core/backtrace or focused reproducer that identifies the caller and
argument source. If the leading hypothesis is confirmed, determine why
`Dict.get` presents a non-nil imported-trait option with a null payload in the
full closure. Preserve cross-module default-method lowering from issue #190;
do not hide corruption by silently skipping the trait. Add one focused
regression, then run one strict bootstrap from an unchanged tracked tree.
