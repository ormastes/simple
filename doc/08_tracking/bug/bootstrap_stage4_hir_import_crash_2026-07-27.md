# Stage 4 HIR Import Crash

## Status

OPEN. The pure-Simple Stage 3 compiler clears the prior address-of parser
failure and HIR null dereference. The unchanged-tree strict follow-up reaches
the end of HIR lowering, then fails because partial/header-only import facades
do not register required glob-exported names.

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

The unchanged-tree strict follow-up passed Stage 2/3 sanity and entered Stage
4. It no longer crashed in `HirLowering.lower_trait`; it reported unresolved
names beginning with `cli_run_file` in
`app.cli._CliMain.args_and_os_commands`, followed by other symbols supplied
through partial/header-only import facades.

- Follow-up Stage 2 SHA-256:
  `00fcb65729acfe1f7bd30e113d7d96bea4cd7ff2e4f596667cda8c6a97c89411`
- Follow-up Stage 3 SHA-256:
  `772f9a2e6d104500c5cd1c661c15b6e0083fd9c936787803bb05f5ad824c17b3`
- Follow-up peak RSS: 5,492,252 KiB
- Follow-up elapsed time: 45:32.18
- Follow-up log:
  `build/bootstrap/cosmos-production-20260727-current/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

## Required Fix

Preserve the nil-dictionary regression as RED until native reference semantics
are corrected. Independently fix partial/header-only facade resolution so
plain and dotted glob re-exports register their symbols, including aliased
traits and re-exported enums. Add focused regressions, then run one strict
bootstrap from an unchanged tracked tree.
