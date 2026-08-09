# Stage-3 self-host SIGSEGV in `FlatAstBridge.module_assembly.flat_ast_to_module`

Date: 2026-08-09
Status: **OPEN — newly revealed, reproducible in one command, first Stage-3 fault
site ever named by a backtrace.**
Area: bootstrap / stage-3 self-host / 10.frontend `_FlatAstBridge` module assembly

## Why this is new

This blocker was previously **unreachable**. Every earlier campaign died before
it: blocker 12 (the dead Stage-2 lexer) stopped runs at lexing, and on pristine
`origin/main` the Stage-2 **link** now fails outright (see
`stage2_native_build_link_undefined_method_symbols_2026-08-09.md`). With the
lexer fixed (`d37b5e578b4`) and the link regression reverted, Stage 3 runs and
reaches module assembly — and crashes there.

## Symptom

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
Segmentation fault (core dumped)
  warning: stage3 self-host failed (exit 139); Stage 4 unavailable
```

`stage3-native-build.log` is **0 bytes** — the crash happens before any build
output is written, which is why no previous run could characterise it.

## Reproduction (one command, instant, 100% reproducible)

```
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  <stage2>/simple native-build src/app/cli/bootstrap_main.spl -o /tmp/out
# -> Segmentation fault (core dumped), exit 139, 43 bytes of output
```

## Backtrace (from the core dump — the first one ever obtained for Stage 3)

```
Program terminated with signal SIGSEGV, Segmentation fault.
#0  compiler__frontend___FlatAstBridge__module_assembly__flat_ast_to_module ()   <+10514>
#1  compiler__frontend___FlatAstBridge__module_assembly__parse_and_build_module_scoped ()
#2  compiler.frontend.frontend.parse_full_frontend_with_scope ()
#3  compiler__driver__driver_source_pipeline_parsing__CompilerDriver.parse_all_impl ()
#4  compiler__driver__driver_orchestration__CompilerDriver.compile ()
#5  app.cli.bootstrap_main.run_native_build_bootstrap ()
#6  main ()

rip 0x4b1ea2  rbp 0x1  rdi 0x2db1f9b0  rsi 0x30
```

`rbp = 0x1` is not a valid frame pointer, consistent with a corrupt/garbage
receiver or an out-of-range arena index rather than a plain null deref.

Source: `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` (51,642 bytes).

## What this rules in and out

- **The lexer bug (blocker 12) is cleared.** `flat_ast_to_module` runs strictly
  *after* lexing and parsing have produced a flat AST, so the Stage-2 binary
  lexed and parsed `bootstrap_main.spl` (21,918 bytes) successfully. `lexer_fatal`
  count across the entire run and the standalone repro: **0**.
- **This is NOT the nil-receiver SIGILL** of
  `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`.
  That fault is SIGILL/`ud2`/exit 132 in `50.mir` lowering, downstream of here.
  This is SIGSEGV/exit 139 in `10.frontend`, phase 1. Both MIR probes
  (`[mir-stmt-caller]`, `[mir-garbage-expr]`) emitted **0 lines** — execution
  never reaches MIR.

## Likely pre-existing, not a regression

No commit in `bfd9284618a..origin/main` touches the flat-AST bridge; the only two
`10.frontend` commits in that window are the two lexer fixes (`d37b5e578b4`,
`ff650c95bf3`). The nearest related change, `c7e82df8c62` *"persist parameter
defaults through the flat-AST bridge"* (touches
`_FlatAstBridge/convert_nodes.spl` and `_Ast/decl_nodes.spl`), **predates**
`bfd9284618a` and was therefore already present in run 4. So this crash was
almost certainly always there, simply masked by the lexer blocker.

## Caveat (stated explicitly)

The Stage-2 binary that produces this crash was built with `36673b6b6a3`
reverted, because pristine `origin/main` cannot link Stage 2 at all. It is
therefore *not* proven that this identical segfault occurs on a pristine tree —
only that it occurs on the nearest tree that can produce a Stage-2 binary. This
caveat cannot be removed until the Stage-2 link regression is fixed.

## Next step

Bisect inside `flat_ast_to_module` with level-gated logging around the module
assembly loop (the function is large and the crash offset `+10514` has no line
info in the stripped Stage-2 binary), or rebuild Stage 2 with debug info to
resolve the offset to a source line.
