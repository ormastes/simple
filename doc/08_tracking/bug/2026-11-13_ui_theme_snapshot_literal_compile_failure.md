# `simple ui` fails to compile on a giant embedded `ThemeRenderSnapshot` literal

Status: confirmed genuine product bug (compile failure, exit 1). The `ui` CLI
does not build on the current seed compiler.

## Evidence

```
simple run src/app/ui/main.spl --help
# exit 1
```

The compiler emits an enormous repeated diagnostic dumping line 9 of a theme
snapshot declaration:

```
9 |     ThemeRenderSnapshot(id: "aetheric_dark", family_id: "aetheric",
      source_reference: ".../simple_os_dark_refined_alignment/code.html",
      source_manifest_sha256: "227d3edb...", material_sha256: "0ad3df5e...",
      composed_css: ":root {\n  --radius-sm: 8px;\n  --radius-md: 12px;\n ...
      /* ~10 KiB of CSS */ ... }",
      background_rgba: 4279111184u32, ..., semantic: ThemeSemanticColors(...))
```

The offending line is a struct literal whose `composed_css` field embeds a
multi-KiB single-line CSS string. The diagnostic repeats the whole literal many
times, which is characteristic of a per-field / per-use compile error over that
one literal rather than a single clean type mismatch. The `ui` log-modes spec
therefore fails all scenarios because the app image never builds.

## Cause and scope

A theme table (likely under `src/app/ui/` or a `config/themes` materialization
step) embeds fully-resolved `ThemeRenderSnapshot` values with very large
single-line string literals. The seed compiler hits a lowering/codegen problem
on that literal (the report is dominated by the echoed source line, not a
specific message). This sits in the UI/theme subsystem owned by another lane
and needs either the literal broken up / moved behind a loader, or a compiler
fix for large string-literal struct fields.

## Correctness gate for a repair

1. Reproduce the minimal case: a struct literal with a single-line string field
   of this size, and confirm whether the seed compiler rejects it independent
   of the theme structs.
2. Decide the fix side: split/loader the theme snapshot literal (UI lane) or
   fix the compiler's large-literal lowering (compiler lane).
3. Re-run `test/02_integration/app/ui_log_modes_spec.spl`; its four red
   scenarios (help, json usage, dot progress, unknown-option json) must pass,
   and `ui_browser_log_modes_spec.spl` (same app family) must stop aborting.
