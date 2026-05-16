# SStack: vscode-plugin-bugfix

## Phase 1: Dev (Intake)

**Type:** bug
**Goal:** Fix VS Code extension bugs so it installs, activates, and runs correctly.

### Acceptance Criteria
- AC-1: `npm install` succeeds without errors
- AC-2: `tsc` compiles without errors
- AC-3: `vsce package` creates a valid VSIX
- AC-4: Extension installs and activates in VS Code
- AC-5: Syntax highlighting works for .spl files
- AC-6: LSP failure handled gracefully (no infinite retries)

## Phase 2-5: Research + Implement

### Bugs Found & Fixed

| # | Bug | Root Cause | Fix |
|---|-----|------------|-----|
| 1 | `npm install` fails | `@vscode/wasm-wasi-lsp@^1.0.0` doesn't exist | Removed from deps (loaded dynamically via try/catch) |
| 2 | Duplicate keys in `package.json` | `"browser"` and `"simple.lsp.mode"` duplicated | Removed duplicates |
| 3 | TypeScript compile errors | Removed wasm packages but imports reference them | Added `@ts-ignore` on dynamic imports |
| 4 | VSIX missing `out/web/extension.js` | `"browser"` field pointed to non-existent file | Removed `"browser"` field |
| 5 | Extension fails to activate | `node_modules` not in VSIX (`--no-dependencies`) | Package without `--no-dependencies` |
| 6 | LSP client infinite retry loop | Server dies, client retries forever | Added `DoNotRestart` error handler |
| 7 | LSP server can't run | `interpret_file()` is non-functional in compiled binary | Graceful warning, basic features work without LSP |

### Known Limitation
- The LSP server (`src/app/lsp/main.spl`) cannot run because the compiled binary's interpreter doesn't execute code (known limitation). The extension works for:
  - TextMate syntax highlighting
  - Test CodeLens
  - AI features (if Copilot installed)
  - Math block rendering
- Full LSP features require compiling the LSP server to a native binary (future work).

## Verification

- [x] AC-1: npm install succeeds
- [x] AC-2: tsc compiles cleanly
- [x] AC-3: VSIX packaged (610 KB, 409 files)
- [x] AC-4: Extension activates in VS Code 1.108.2
- [x] AC-5: Syntax highlighting works (comments, keywords, types, strings)
- [x] AC-6: LSP failure shows clean notification, no retry loop

## Files Changed

- `src/app/vscode_extension/package.json` — removed duplicate keys, fixed deps, removed browser field
- `src/app/vscode_extension/src/extension.ts` — auto-detect server path, DoNotRestart error handler, better warning messages
- `src/app/vscode_extension/src/wasm/wasmLspBridge.ts` — @ts-ignore for optional dynamic imports

## Status: COMPLETE
