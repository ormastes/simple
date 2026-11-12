# Windows git symlinks break app module resolution (2026-11-12)

## Repro

On Windows checkouts, git symlinks defined as textual file entries (not real NTFS symlinks, per `.git/config` `core.symlinks=false` or manual entry creation) fail to resolve as modules.

Specifically, directories like:
- `src/app/cmm_lsp` (symlink to `examples/10_tooling/trace32_tools/cmm_lsp`)
- `src/app/t32_lsp_mcp` (symlink to `examples/10_tooling/trace32_tools/t32_lsp_mcp`)
- `src/app/mcp_t32` (symlink to `examples/10_tooling/trace32_tools/t32_mcp`)
- `src/app/t32_cli` (symlink to `examples/10_tooling/trace32_tools/t32_cli`)

materialize on Windows as **plain text files** (120 bytes, containing a relative path string), not as directory entries.

A `use app.cmm_lsp.*` or `use app.mcp_t32.*` statement then fails with:
```
error[module_not_found]: module 'app.cmm_lsp' not found
  note: searched in: src/app/cmm_lsp.spl, src/app/cmm_lsp/__init__.spl
```

## Impact

- Modules cannot import helpers from the symlinked directories.
- Desktop/Windows development is blocked for code that depends on these modules.
- CI/Linux builds work (real symlinks resolve correctly).

## Root Cause

Windows does not natively support POSIX symlinks. Git on Windows can:
1. Create and track real NTFS symlinks (requires elevated privileges, `core.symlinks=true`).
2. Fall back to text files with the symlink target as content (`core.symlinks=false`, default).

Option 2 is the default on Windows and on clones that do not have elevated privileges. The text-file representation is for version control only—it should not be checked out as the actual artifact.

## Possible Fixes

1. **`core.symlinks=true`** (requires elevated privileges on first clone):
   ```bash
   git clone --config core.symlinks=true https://github.com/ormastes/simple.git
   # Or on an existing clone:
   git config core.symlinks true
   git reset --hard HEAD
   ```
   Enables real NTFS symlinks. Not always available on restricted systems.

2. **Module loader follows symlink-text files**:
   Modify the compiler's module resolution to:
   - Detect text files under `src/app/` that match the symlink format (exactly one line, relative path ending in `/`).
   - Follow the path to the actual module directory.
   
   Example: `src/app/cmm_lsp` is a text file containing `../examples/10_tooling/trace32_tools/cmm_lsp\n` → resolve to `examples/10_tooling/trace32_tools/cmm_lsp/__init__.spl`.

3. **Replace symlinks with stubs or duplicates**:
   - Replace text symlinks with stub `__init__.spl` files that re-export from the canonical location.
   - Or accept duplication (less maintainable).

## Recommendation

Fix 2 is the most portable: it allows Windows clones without privileges to work, and Linux clones are unaffected (real symlinks still resolve as before). The module loader is already path-relative, so the added logic is a conditional fallback on Windows when a text file is discovered where a directory is expected.

## Files Affected

- `src/app/cmm_lsp` → `examples/10_tooling/trace32_tools/cmm_lsp`
- `src/app/t32_lsp_mcp` → `examples/10_tooling/trace32_tools/t32_lsp_mcp`
- `src/app/mcp_t32` → `examples/10_tooling/trace32_tools/t32_mcp`
- `src/app/t32_cli` → `examples/10_tooling/trace32_tools/t32_cli`
