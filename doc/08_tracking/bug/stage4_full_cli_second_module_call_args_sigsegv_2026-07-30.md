# Stage 4 full CLI second-module call-argument SIGSEGV

## Status

SIGSEGV fixed on 2026-07-31 by replacing `_hir_expr_symbol`'s fragile
`SymbolId?` transport with the existing invalid `SymbolId(-1)` sentinel and
checking `is_valid()` at every caller. The rebuilt Stage 4 lowers
`log_modes.spl` completely and now stops normally at the next independent
module-surface alias fingerprint error.

## Reproduction

From the dedicated worktree at `3c495fc044a` or later:

```sh
env SIMPLE_NO_STUB_FALLBACK=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --no-mcp --jobs=half
```

The refreshed Rust seed/runtime build succeeds. Stage 2 and Stage 3 compile and
pass bootstrap sanity. Stage 4 exits 139 (SIGSEGV); its retained log is:

`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

The final bounded trace is:

```text
phase3:hir:file:done src/app/cli/main.spl module=app.cli.main
phase3:hir:file:start src/lib/nogc_async_mut/cli/log_modes.spl
[hir-lower] lower_expr:kind
[hir-lower] lower_expr:kind
Segmentation fault
```

The crash occurs while lowering the named arguments of
`SimpleLogOptions.defaults()`.

## Reduction evidence

- `log_modes.spl` alone compiles and links with the verified Stage 3 compiler.
- The existing `src/app/install/main.spl` entry closure compiles 61 modules and
  links with the same Stage 3 compiler.
- The full CLI closure crashes at the same expression with streaming surfaces
  enabled and disabled, so streaming reclamation is not the root cause.
- The admitted Stage 2 and Stage 3 compilers crash at the identical expression,
  so this is shared Stage 4 HIR state rather than a Stage 3 self-host codegen
  regression.
- A three-source reproducer (`app.cli.main`, `log_modes`, and its physical
  alias) crashes in about 1.2 seconds at heap registry ~5,350. Its entry contains
  only a `use std.cli.log_modes.{...}` statement. Both plain `use` and
  `export use` reproduce, eliminating export registration, module count,
  concurrency, and memory pressure.
- The passing 61-module install entry has executable functions before
  `log_modes`; the reduced failing entry is import-only. The next investigation
  should therefore target first-function/first-`[HirCallArg]` initialization
  after an empty entry module.

## Next discriminating checks

1. Run the 1.2-second reduced case under GDB and capture the native backtrace;
   the admitted compiler includes DWARF and is not stripped.
2. Add one trivial function to the reduced entry. If that passes, compare the
   first call-expression/`HirCallArg` initialization against an import-only
   entry and fix the shared HIR owner, not the CLI source.
3. Keep the reduced case as the focused regression check, then run the strict
   full bootstrap once.

## Done condition

The strict full bootstrap completes Stage 4, its `-c 'print(1+1)'` smoke returns
`2`, and the resulting pure-Simple CLI runs the focused evidence tests without
the test-ABI fallback.

## Fix verification

- GDB showed `_hir_expr_symbol` returning nil while the Stage 4 optional
  presence path entered and dereferenced the nil payload in
  `HirLowering.lower_hir_expr`.
- Rebuilt Stage 2 and Stage 3 both passed sanity.
- Stage 4 passed the former faulting constructor and completed
  `src/lib/nogc_async_mut/cli/log_modes.spl`.
- The new bounded failure is
  `Module surface/source fingerprint mismatch for
  src/lib/nogc_async_mut/cli/log_modes.spl`, after lowering, not a signal.
