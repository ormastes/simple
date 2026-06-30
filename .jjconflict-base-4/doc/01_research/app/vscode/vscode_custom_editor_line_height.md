# VSCode Custom Editor: Line Height, Images & Variable Height Rendering

## User Request
> vscode custom editor creation. and how editor check line height. how make add image and make line height thicker. research for new simple vscode plugin. research with agent teams

## Summary

**The fundamental constraint:** Monaco (VSCode's built-in editor) does NOT support variable line heights. Every line has the same pixel height. There is no extension API to change individual line heights.

**The solution:** Custom Editor (`CustomTextEditorProvider`) with a webview containing CodeMirror 6, which natively supports variable-height widgets.

**Current state:** The Simple VSCode extension already implements both paths — a decoration-based approach (clamped SVGs in native editor) and a CodeMirror 6 custom editor (natural height rendering).

---

## 1. VSCode Custom Editor API

### Three Provider Types

| Type | Backing Model | Undo/Save | Use Case |
|------|--------------|-----------|----------|
| `CustomTextEditorProvider` | `TextDocument` (VSCode managed) | Automatic | Text-based files with rich rendering |
| `CustomReadonlyEditorProvider<T>` | Custom `CustomDocument` | N/A | Binary viewers (images, hex) |
| `CustomEditorProvider<T>` | Custom `CustomDocument` | Manual (you fire events) | Binary editors with edit support |

### Registration

**package.json:**
```json
"customEditors": [{
  "viewType": "simple.mathSourceEditor",
  "displayName": "Simple Math Source Editor",
  "selector": [{ "filenamePattern": "*.spl" }],
  "priority": "option"   // "default" or "option"
}]
```

**Code:**
```typescript
vscode.window.registerCustomEditorProvider(viewType, provider, {
  webviewOptions: { retainContextWhenHidden: true },
  supportsMultipleEditorsPerDocument: false,
});
```

### Lifecycle

1. User opens a `.spl` file → VSCode calls `resolveCustomTextEditor(document, webviewPanel, token)`
2. Provider fills `webviewPanel.webview.html` with HTML
3. Webview sends `'ready'` → Host sends initial sync
4. Bi-directional sync via `postMessage()`:
   - Webview → Host: edits, selection changes
   - Host → Webview: document changes, rendered content

---

## 2. Line Height: The Core Limitation

### Monaco's Fixed Line Height
- `editor.lineHeight` setting applies **uniformly to ALL lines**
- No extension API exposes `changeViewZones()` (Monaco's internal mechanism for inserting content between lines)
- Decorations render within the fixed line box — they cannot expand it
- If content is taller than line height, it either **overflows** (overlaps adjacent lines) or must be **clamped**

### What Decorations CAN Do
- `contentIconPath` in `before`/`after` pseudo-elements — shows an SVG/PNG
- `width`, `height` control the image box CSS (NOT the editor line)
- `textDecoration: 'none; vertical-align: middle'` for alignment
- `gutterIconPath` — ~16x16 icon in gutter only
- **Cannot:** insert arbitrary HTML, expand line height, or create DOM elements between lines

### The "HEIGHT FIT PATH" (Current Implementation)
```typescript
const MAX_INLINE_HEIGHT_EM = 3.0;  // Clamp tall SVGs to fit in line
const inlineScale = Math.min(1.0, MAX_INLINE_HEIGHT_EM / svgResult.heightEm);
```
This scales tall equations DOWN to fit within the fixed line box.

---

## 3. How to Add Images & Make Lines Thicker

### Strategy A: Native Editor Decorations (Fixed Height, Quick Preview)

```typescript
// SVG rendered by MathJax, cached to disk
svgDecorations.push({
  range: block.fullRange,
  renderOptions: {
    before: {
      contentIconPath: svgUri,       // Cached SVG file
      width: `${widthEm}em`,
      height: `${heightEm}em`,      // Clamped to MAX_INLINE_HEIGHT_EM
      textDecoration: `none; vertical-align: ${verticalAlign}`,
    },
  },
});
```

**Limitations:** Cannot make lines taller. Tall content is scaled down.

### Strategy B: Custom Editor with CodeMirror 6 (Variable Height, Full Fidelity)

CodeMirror 6 **natively supports variable line heights**. It measures each line's DOM height dynamically.

**Inline replacement widget (expands line height automatically):**
```typescript
class MathWidget extends WidgetType {
  toDOM(): HTMLElement {
    const wrap = document.createElement('span');
    wrap.className = 'cm-math-widget';
    wrap.innerHTML = this.html;  // KaTeX HTML at NATURAL height
    return wrap;
  }
}

builder.add(block.from, block.to,
  Decoration.replace({
    widget: new MathWidget(html, prefix, content),
  })
);
```

**Block-level widget (inserts full-width content BETWEEN lines):**
```typescript
class DiagramWidget extends WidgetType {
  toDOM(): HTMLElement {
    const div = document.createElement('div');
    div.className = 'cm-block-widget';
    div.innerHTML = this.svgHtml;
    return div;
  }
  get estimatedHeight(): number { return 120; }
}

builder.add(lineEnd, lineEnd,
  Decoration.widget({
    widget: new DiagramWidget(renderedHtml),
    block: true,   // KEY: inserts as full-width block between lines
    side: 1,       // 1 = after line, -1 = before line
  })
);
```

**Line decoration (make specific lines taller):**
```typescript
Decoration.line({
  attributes: { style: 'min-height: 80px; padding: 8px 0;' }
})
```

### Strategy C: When to Use Each

| Content Type | Mechanism | Location |
|---|---|---|
| Simple inline math (`m{ x + y }`) | `Decoration.replace` inline widget | CodeMirror custom editor |
| Tall expressions (`m{ frac(...) }`) | Same — CodeMirror auto-expands | CodeMirror custom editor |
| Block diagrams, matrices, images | `Decoration.widget({ block: true })` | CodeMirror custom editor |
| Quick preview in native editor | `contentIconPath` SVG (clamped) | Monaco via decorations |

---

## 4. Adding Images in the Custom Editor

### Inline Images
```typescript
class ImageWidget extends WidgetType {
  constructor(private src: string, private alt: string) { super(); }
  toDOM(): HTMLElement {
    const img = document.createElement('img');
    img.src = this.src;
    img.alt = this.alt;
    img.style.maxHeight = '200px';
    img.style.verticalAlign = 'middle';
    return img;
  }
}
```

### Block Images (Between Lines)
```typescript
class BlockImageWidget extends WidgetType {
  toDOM(): HTMLElement {
    const wrap = document.createElement('div');
    wrap.className = 'cm-image-block';
    const img = document.createElement('img');
    img.src = this.src;
    img.style.maxWidth = '100%';
    wrap.appendChild(img);
    return wrap;
  }
}

// Insert after the line containing the image reference
builder.add(lineEnd, lineEnd, Decoration.widget({
  widget: new BlockImageWidget(imageUri),
  block: true,
  side: 1,
}));
```

### CSS for Block Widgets
```css
.cm-image-block, .cm-math-block-widget {
  display: block;
  width: 100%;
  padding: 12px 16px;
  margin: 4px 0;
  border-radius: 6px;
  background: color-mix(in srgb, var(--vscode-editor-foreground) 4%, transparent);
  border-left: 3px solid var(--vscode-textLink-foreground);
  text-align: center;
  overflow: auto;
}
```

---

## 5. Webview Security & Communication

### Content Security Policy
```html
<meta http-equiv="Content-Security-Policy"
  content="default-src 'none';
           style-src ${cspSource} 'unsafe-inline';
           font-src ${cspSource};
           img-src ${cspSource} data:;
           script-src 'nonce-${nonce}';">
```

### Message Protocol
```typescript
// Extension → Webview
webviewPanel.webview.postMessage({ type: 'sync', text, blocks });

// Webview → Extension (inside webview JS)
const vscode = acquireVsCodeApi();
vscode.postMessage({ type: 'editAll', source: newText });

// Extension receives
webviewPanel.webview.onDidReceiveMessage(async (msg) => {
  if (msg.type === 'editAll') { /* apply edit */ }
});
```

### Local Resources
```typescript
webviewPanel.webview.options = {
  enableScripts: true,
  localResourceRoots: [katexDistUri, imagesUri],
};
const webviewUri = webview.asWebviewUri(localFileUri);
```

---

## 6. Alternative Approaches (Evaluated & Rejected)

| Approach | Why Not |
|---|---|
| Monaco `IViewZone` | Not exposed in extension API, internal only |
| Notebook API | Requires cell paradigm, breaks continuous code editing |
| CodeLens | Fixed height slot, text-only, no images |
| Hover tooltips | Only visible on hover, not persistent |
| Webview panels (side) | Preview only, not inline with editing |

---

## 7. Current Architecture (Simple Extension)

```
┌─────────────────────────────────────────────┐
│         NATIVE EDITOR PATH                  │
│  (Fixed line height, quick preview)         │
│                                             │
│  mathDecorationProvider.ts                  │
│  ├── Detect math blocks                    │
│  ├── Render to SVG (MathJax)               │
│  ├── Cache SVG to disk                     │
│  ├── Clamp height to 3.0em                 │
│  ├── Apply decoration with contentIconPath  │
│  └── Cursor-aware reveal (hide on focus)   │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│         CUSTOM EDITOR PATH                  │
│  (Variable line height, full fidelity)      │
│                                             │
│  mathCustomEditor.ts (provider)             │
│  ├── resolveCustomTextEditor()             │
│  ├── Bi-directional sync                   │
│  └── KaTeX rendering on host side           │
│                                             │
│  mathEditorWebview.ts (webview)             │
│  ├── CodeMirror 6 editor                   │
│  ├── MathWidget (inline, natural height)    │
│  ├── Cursor-aware reveal                   │
│  └── simpleLang.ts (syntax highlighting)    │
└─────────────────────────────────────────────┘
```

---

## 8. Recommendations for New Plugin Enhancement

### 8.1 Add Block-Level Math Widgets
Currently only `Decoration.replace` (inline). Add `Decoration.widget({ block: true })` for tall content:
- Matrices, cases environments, multi-line aligned equations
- Diagrams and charts
- Code output/results

### 8.2 Add Image Support
- Detect image references in `.spl` files (e.g., `img("path.png")` or `diagram(...)`)
- Render as block widgets with natural dimensions
- Support base64 data URIs for self-contained images

### 8.3 Heuristic for Inline vs Block
```typescript
function shouldRenderAsBlock(block: MathBlock): boolean {
  return block.content.includes('cases(') ||
         block.content.includes('matrix(') ||
         block.content.includes('pmatrix(') ||
         block.content.includes('align(') ||
         estimatedHeight(block) > 3.0;  // em
}
```

### 8.4 Keep Dual-Mode Architecture
- Native editor decorations: fast, "good enough" preview with clamped SVGs
- Custom editor: full-fidelity variable-height rendering
- Both modes should coexist — user chooses via "Open With..."

---

## References
- VSCode Custom Editor API: `vscode.d.ts` lines 8970-9278
- CodeMirror 6 Decorations: https://codemirror.net/docs/ref/#view.Decoration
- KaTeX: https://katex.org/
- MathJax: https://www.mathjax.org/
- Current impl: `src/app/vscode_extension/src/math/`
