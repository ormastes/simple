# VS Code Extension Webview Re-enable Plan

## Current Safe Base

- Rich custom editor opens again in a fresh isolated VS Code extension host.
- Main editor rendering works for the current math sample.
- Optional custom-editor GUI extras are intentionally disabled:
  - `ENABLE_TEST_LINE_WIDGETS = false`
  - `ENABLE_SYMBOL_HOVER = false`

Verified on:
- `src/app/vscode_extension/examples/phase2-ide-surfaces.spl`
- Screenshot: `artifacts/phase2-baseline-restored.png`

## Actual Crash Point Found

- The webview bundle was failing before boot because `TestRunWidget` extended `WidgetType`, but `WidgetType` had been imported as a type-only symbol.
- Runtime symptom:
  - `last error: WidgetType is not defined`
- Impact:
  - one optional custom-editor widget crashed the entire webview boot path

## Containment Rule Going Forward

- No optional custom-editor feature may be defined in a way that can crash module evaluation.
- Optional features must be guarded so the editor can still boot in plain rich-render mode.
- Re-enable features one at a time, with a fresh isolated VS Code host after each step.
- Close all Code windows after each verification run.

## Re-enable Order

1. Math spacing CSS only
   - low risk
   - no runtime widget logic
2. Custom-editor symbol hover
   - DOM overlay only
   - no editor decoration class inheritance risk
3. Custom-editor test run widgets
   - highest risk of the current tranche
   - depends on runtime widget classes and click routing

## Verification Gate Per Step

1. `npm run compile` in `src/app/vscode_extension`
2. quit all Code windows
3. open fresh isolated extension-development host
4. open `phase2-ide-surfaces.spl`
5. verify:
   - editor opens
   - no blank webview
   - no crash loop
   - logs remain clean except unrelated VS Code update noise
6. close Code

