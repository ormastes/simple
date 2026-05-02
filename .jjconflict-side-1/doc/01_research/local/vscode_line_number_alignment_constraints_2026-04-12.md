<!-- codex-research -->
# Local Notes: Line-Number Alignment Constraints

Date: 2026-04-12

## Relevant Current Code

- Current migrated custom editor:
  - [src/app/vscode_extension/src/richCustomEditor.ts](../../../src/app/vscode_extension/src/richCustomEditor.ts)
  - [src/app/vscode_extension/src/webview/richEditorWebview.ts](../../../src/app/vscode_extension/src/webview/richEditorWebview.ts)
- Rendered widget blocks already exist:
  - [mathWidget.ts](../../../src/app/vscode_extension/src/webview/widgets/mathWidget.ts)
  - [imageWidget.ts](../../../src/app/vscode_extension/src/webview/widgets/imageWidget.ts)
- Prior repo research already noted the key platform limit:
  - [src/app/vscode_extension_old/doc/research_domain_math_editor_panel.md](../../../src/app/vscode_extension_old/doc/research_domain_math_editor_panel.md)
  - [doc/01_research/local/vscode_rich_editor.md](../local/vscode_rich_editor.md)

## Local Conclusion

The current implementation is already on the only platform path that gives reliable control over variable-height rendering: a custom editor backed by a webview.

That means the line-number alignment problem should be solved inside the webview-owned editor UI, not by trying to restyle the host VS Code editor gutter.

## Local Recommendation

- Short term: own gutter alignment in the current webview editor.
- Medium term: if CodeMirror gutter behavior remains awkward, evaluate swapping the webview editor core to Monaco and use Monaco `IViewZone.marginDomNode` for centered gutter content.
