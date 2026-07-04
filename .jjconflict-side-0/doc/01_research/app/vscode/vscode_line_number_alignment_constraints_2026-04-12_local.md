<!-- codex-research -->
# VS Code / Monaco / Electron Line-Number Alignment Constraints

Date: 2026-04-12

## Scope

Research question: what official or public platform support exists for line-number alignment on variable-height lines, especially for a VS Code extension that uses a custom editor or webview?

## Official Constraints

### 1. VS Code extensions cannot style the native editor DOM

VS Code's extension capability docs explicitly say extensions have **no DOM access** to the VS Code UI and cannot apply **custom style sheets** to VS Code itself.

- VS Code Extension Capabilities Overview:
  - "Extensions have no access to the DOM of VS Code UI."  
    https://code.visualstudio.com/api/extension-capabilities/overview
  - "You cannot write an extension that applies custom CSS to VS Code..."  
    https://code.visualstudio.com/api/extension-capabilities/overview
  - "A custom style sheet provided by users or extensions..." is disallowed because DOM/class names are internal.  
    https://code.visualstudio.com/api/extension-capabilities/overview

Implication: an extension cannot directly restyle the native Monaco gutter or native line-number cells in the built-in text editor.

### 2. Custom editors/webviews can fully control their own DOM

VS Code's extension docs state that if an extension needs a fully customized UI, it should use the **Webview API**. Custom editors are built on webviews.

- Extension Capabilities Overview:
  - "if your extension needs a fully customized user interface, use the Webview API to build your own document preview or UI using standard HTML, CSS, and JavaScript."  
    https://code.visualstudio.com/api/extension-capabilities/overview
- Custom Editor guide:
  - custom editors allow extensions to create "fully custom experiences for readonly or editable resources."  
    https://code.visualstudio.com/api/extension-guides/custom-editors
- Webview guide:
  - webviews use standard HTML/CSS/JS, and can be themed with VS Code CSS variables such as `--vscode-editor-font-family`, `--vscode-editor-font-weight`, and `--vscode-editor-font-size`.  
    https://code.visualstudio.com/api/extension-guides/webview

Implication: if line-number alignment must be controllable, the extension should own the gutter UI inside a custom editor/webview.

### 3. Monaco now has variable line-height support, but VS Code says it is not yet available to extensions

VS Code 1.100 release notes added Monaco support for variable line heights via `IModelDecorationOptions`, but the same note says:

- "This work is not yet available to extensions, but will roll out after some more testing."  
  https://code.visualstudio.com/updates/v1_100

Implication: native per-line height support exists in Monaco internals, but an extension cannot rely on that being exposed through current VS Code extension APIs.

## Monaco Capabilities Relevant Inside a Webview-Owned Editor

These APIs matter if the extension embeds Monaco inside its own webview, rather than trying to modify the host VS Code editor.

### 1. Monaco has global editor line-height and line-number options

- `IEditorOptions.lineHeight?: number`
- `IEditorOptions.lineNumbers?: LineNumbersType`

Source:
- https://microsoft.github.io/monaco-editor/typedoc/interfaces/editor_editor_api.editor.IEditorOptions.html

Constraint: these are editor-owned Monaco options, not VS Code extension API knobs for the native editor.

### 2. Monaco exposes custom line-height decorations on the model

`ITextModel` includes:
- `getCustomLineHeightsDecorations(...)`

Source:
- https://microsoft.github.io/monaco-editor/typedoc/interfaces/editor.ITextModel.html

This aligns with the VS Code 1.100 note that Monaco internally understands per-line line heights.

### 3. Monaco view zones can reserve vertical space and can render a gutter-side DOM node

`IViewZone` includes:
- `domNode`
- `heightInLines` / `heightInPx`
- `marginDomNode`

Source:
- https://microsoft.github.io/monaco-editor/typedoc/interfaces/editor.IViewZone.html

Implication: inside a Monaco instance that the extension owns in a webview, a plausible design is:
- add vertical space with a view zone
- place a custom line-number node in `marginDomNode`
- vertically center that node relative to the tall content

This is public Monaco API and does not depend on undocumented CSS selectors.

## Electron-Level Options

Electron itself exposes host-window capabilities such as:
- `webContents.insertCSS(...)`
- `webContents.executeJavaScript(...)`

Source:
- https://www.electronjs.org/docs/latest/api/web-contents

Constraint: that is only useful if you control the Electron `BrowserWindow` / `webContents`. A normal VS Code extension does not get that control. Combined with VS Code's "No DOM Access" / "No custom style sheets" rules, Electron-level CSS injection is **not a supported extension solution** for altering the native VS Code editor gutter.

## Ranked Solution Options

### Option 1. Custom editor/webview owns the entire gutter and content

Description:
- use the current custom editor path
- render line numbers in your own DOM
- vertically center them with normal CSS layout

Pros:
- fully supported by VS Code webview/custom editor model
- easiest way to guarantee alignment with variable-height content
- easy to theme using VS Code CSS variables

Cons:
- you own more editor behavior
- native editor behavior must be replicated or intentionally reduced

Fit:
- best option for the current migration path

### Option 2. Monaco inside the webview, using public Monaco APIs

Description:
- embed Monaco in the custom editor webview
- use `IViewZone.heightInPx` / `heightInLines` for tall content
- use `marginDomNode` for a centered gutter-side element

Pros:
- still public API
- stronger text-editor semantics than fully custom DOM
- explicit gutter-side placement support

Cons:
- more implementation complexity than Option 1
- still separate from the native VS Code editor

Fit:
- good if you want Monaco behavior inside the webview without depending on VS Code internals

### Option 3. Wait for VS Code to expose native variable line-height support to extensions

Description:
- keep using the normal source editor
- postpone alignment work until the Monaco feature is extension-accessible

Pros:
- preserves native editor/gutter behavior

Cons:
- blocked today by the extension API gap explicitly called out in VS Code 1.100
- no delivery timeline promised in the cited note

Fit:
- only valid if native-editor integration is mandatory and schedule is flexible

### Option 4. Electron/CSS injection into the host window

Description:
- patch VS Code, use unsupported hacks, or own an Electron fork

Pros:
- could theoretically alter native gutter layout

Cons:
- not supported for marketplace extensions
- conflicts with VS Code extension restrictions
- brittle against internal DOM changes

Fit:
- not recommended for this project

## Recommendation

For a shippable VS Code extension, the practical and supported answer is:

1. do not try to restyle the native VS Code gutter
2. keep the custom editor/webview architecture
3. either:
   - own the gutter completely in the webview, or
   - embed Monaco inside the webview and use `IViewZone.marginDomNode` plus reserved vertical space

Given the current repo state, Option 1 is the lowest-risk path. Option 2 is the best "editor-like" upgrade path if tighter Monaco behavior is needed later.
