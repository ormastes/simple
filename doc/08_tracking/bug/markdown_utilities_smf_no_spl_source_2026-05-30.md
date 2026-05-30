# std.common.markdown.utilities resolves to smf-only, no spl source

Date: 2026-05-30
Status: Open
Severity: Medium

## Symptom

`test/system/editor_markdown_document_decor_spec.spl` fails with:

```
Cannot resolve module: std.common.markdown.utilities
```

## Evidence

- `find src/lib/common/markdown -type f` shows:
  - `adapter.spl` (only `.spl` source in directory)
  - `block.smf`, `inline.smf`, `mod.smf`, `parse.smf`, `render.smf`, `types.smf`, `utilities.smf` (compiled binaries, no corresponding `.spl` source)
- The `utilities.smf` file exists at `src/lib/common/markdown/utilities.smf` but there is no `utilities.spl` source alongside it.
- Other tests that use `std.editor.backend.gui_backend.*` (stored in `70.backend/`) resolve correctly, ruling out a general numbered-directory issue.
- The module resolver is failing on `utilities` specifically, suggesting `.smf`-only modules in `src/lib/common/markdown/` are not resolved from the test environment.

## Root Cause Hypothesis

The `.smf` files in `src/lib/common/markdown/` are pre-compiled artifacts without corresponding `.spl` sources. If the test runner or module resolver requires a `.spl` source file to resolve a module (and does not fall back to `.smf` in test/interpreter mode), all of `block`, `inline`, `parse`, `render`, `types`, and `utilities` will fail to resolve. The test reports `utilities` first because it appears first in the import order after the first resolvable module.

## Expected

Either:
1. The `.spl` source files for all modules in `src/lib/common/markdown/` are restored/created, or
2. The module resolver is fixed to resolve `.smf` modules in interpreter/test mode.

## Next Probe

- Verify whether `std.common.markdown.block` (also `.smf`-only) fails with the same error.
- Check git log for when the `.spl` sources were removed: `git log --diff-filter=D --name-only -- 'src/lib/common/markdown/*.spl'`.
- If deleted: restore from git history. If never existed: write the `.spl` sources.

## Affected tests

- `test/system/editor_markdown_document_decor_spec.spl`
