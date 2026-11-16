# Windows checkout: symlinked `src/app` dirs are text stubs, so the full CLI closure cannot compile

- **ID:** windows_symlink_stub_app_dirs_break_cli_closure_2026-11-14
- **Severity:** P1 (blocks the Phase 3 full-CLI native build on Windows)
- **Status:** open
- **Found:** 2026-11-14, Phase 3 LLVM build (`p2.exe native-build --entry src/app/cli/_CliMain/main_and_help.spl`), Windows host, Git Bash, `core.symlinks=false`

## Symptom

```
HIR lowering error in src/app/cli/_CliMain/main_and_help.spl: unresolved name: t32_cli_main at .../main_and_help.spl:358:16
HIR lowering error in src/app/cli/_CliMain/main_and_help.spl: unresolved name: t32_cli_main at .../main_and_help.spl:742:16
[hir-reexport-chase-unresolved] facade=app.__init__ item=t32_cli_main ...
```

The import itself is fine: `main_and_help.spl:53` has `use app.t32_cli.mod.{t32_cli_main}`.

## Root cause

Git tracks four `src/app` entries as symlinks (mode `120000`) into
`examples/10_tooling/trace32_tools/`:

- `src/app/t32_cli`
- `src/app/mcp_t32`
- `src/app/cmm_lsp`
- `src/app/t32_lsp_mcp`

With `core.symlinks=false` (the Git for Windows default without developer mode or admin), git writes
each one as a 47-byte text file holding the link target, for example
`../../examples/10_tooling/trace32_tools/t32_cli`. The SCV snapshot copies that stub, so
`app.t32_cli.mod` does not exist and every name imported from it is unresolved. All checked
Windows trees have the stub: `/c/dev/simple`, `/c/dev/wt-lane2`, `/c/dev/phase2-wt`, `/c/dev/wt-p3src`.

Related: `bootstrap_pinned_archive_symlink_extraction_fails_windows_2026_11_11.md` (the same
symlink class breaks pinned-archive extraction) and
`compiler_cli_build_run16_facade_brace_export_and_t32_relative_imports_2026-11-12.md`
(the Class B relative-import fix, which assumed the symlinks are real directories).

## Workaround in use

Before the build, the Phase 3 lane replaced the four stubs in the build tree with real
Windows junctions (`mklink /J`) to the `examples/` targets. Plain copies do not work: compile
admission then fails with `SCV-E-ADMISSION: directory-alias-inventory-invalid`, because the
alias inventory expects each tracked link to resolve outside itself. This was not done in the
source tree.

## Candidate fixes (owner decision)

1. Replace the four symlinks with real directories or `.spl` facade modules under `src/app/`
   that re-export from a source root the build includes.
2. Have the build or SCV snapshot detect a `120000` stub on a `core.symlinks=false` host and
   resolve it to its target, or fail closed with a clear diagnostic. Today the failure surfaces
   much later as an unrelated `unresolved name`.

## Second finding from the same build: the seed is more lenient than Phase 2

The Phase 2 compiler (pure Simple) rejected three browser-engine renderer modules that the
Rust seed accepts:

- `simple_web_html_layout_renderer_core.spl` uses `decl_get` (defined in
  `simple_web_html_layout_renderer_foundation.spl`) but never imports it. Result: 10 `unresolved name: decl_get` errors.
- `simple_web_html_layout_renderer_layout_foundation.spl` and `..._layout_engine.spl` use
  `Style` (`class Style` in `simple_web_html_layout_renderer_style.spl:7`) but never import it.
  The explicit `export use` chain paint_primitives -> layout_foundation -> layout_engine never lists it.
  Result: 216 `unresolved type: Style` errors.

The seed resolves these names transitively and the Phase 2 compiler does not, so a seed-green
`simple test` does not prove a module compiles under the self-hosted compiler. The missing
imports are fixed in PR work/phase3-compile-fixes-1. That PR does not change the seed's
leniency, which stays open here.

A single-file seed `check` of `layout_foundation.spl` also reports `unresolved type: HNode` and
`HtmlChildIndex`. The Phase 2 build did not report these as fatal; it showed them only as
`hir-reexport-chase-unresolved` warnings. Watch for them if import resolution gets stricter.
