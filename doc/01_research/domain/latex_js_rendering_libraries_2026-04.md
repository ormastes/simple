# LaTeX JS/TS Rendering Libraries — Research

## User Request
> find latex grammar support js/ts libraries and compare. for vscode, can use that as a default render for match blocks? and add pure simple latex renderer as feature request. first search latex engines and suggest what to use what is better than others

## Date
2026-04-09

---

## Current State

The VS Code extension already has a math rendering system at `src/math/`:
- **Block detection**: Regex for `m{}`, `loss{}`, `nograd{}` blocks
- **Conversion**: `simpleToUnicode()` (Unicode text) and `simpleToLatex()` (LaTeX markup) in `mathConverter.ts`
- **Inline decorations**: Unicode preview via `contentText` in editor decorations (cursor-aware reveal)
- **Hover**: VSCode built-in KaTeX renders `$$...$$` markdown in hover tooltips (fallback mode)
- **Preview panel**: Offline HTML webview showing Unicode + LaTeX source (no runtime renderer)
- **No external LaTeX library** in `package.json` dependencies

---

## Library Comparison

### Full Rendering Engines

| Feature | **KaTeX** | **MathJax v4** | **Temml** | **LaTeX.js** |
|---|---|---|---|---|
| npm package | `katex` | `mathjax` | `temml` | `latex.js` |
| Unpacked size | 4.0 MB | 20 MB | 2.2 MB | 14.0 MB |
| Min+gzip JS | ~69 KB (+fonts) | ~59 KB (loader; SVG pipeline larger) | ~15-20 KB (+~10 KB fonts) | Very large |
| Output format | HTML+CSS (spans+webfonts) | HTML+CSS, **SVG**, MathML | **MathML** only | HTML5 |
| SVG output | **No** (not planned) | **Yes** — `tex2svg()` first-class | No | No |
| Node.js | Yes — `renderToString()` | Yes — `liteAdaptor` | Yes — MathML string | Yes |
| Dependencies | Zero | Zero | Zero | Has deps |
| Speed | Fastest (~2-5x faster) | Slower but closing gap | Fast | Slow |
| LaTeX coverage | ~80% common math | Most comprehensive | Broader than KaTeX | Full document |
| Unicode output | No | No | No | No |
| License | MIT | Apache-2.0 | MIT | MIT |
| Maintenance | Active (2025) | Active (v4.1.1) | Active (Sept 2025) | Less active |

### LaTeX-to-Unicode Libraries

| Feature | **unicodeit** | **latex-to-unicode-converter** |
|---|---|---|
| npm package | `unicodeit` | `latex-to-unicode-converter` |
| Size | 299 KB | 405 KB |
| Coverage | Greek, math symbols, scripts | Comprehensive: blackboard bold, Fraktur, calligraphic, combining diacritics |
| Output | Plain Unicode text | Plain Unicode text |
| License | MIT | MIT |

### Parsing/AST Libraries (no rendering)

| Feature | **unified-latex** | **latex-utensils** |
|---|---|---|
| Size | 135 KB | 933 KB |
| Purpose | Parse LaTeX to AST | Parse LaTeX/BibTeX to AST |
| Used by | Academic tools | LaTeX Workshop |

---

## VS Code Rendering Surface Analysis

### 1. Webview Panel — Best quality
- Full browser environment, any library works
- **KaTeX** best choice: fast, small, beautiful HTML+CSS output
- Load CSS + fonts as webview resources
- Disadvantage: separate panel, not inline

### 2. Hover Tooltips — In-context
- VS Code hovers accept `MarkdownString`
- SVG data URIs **broken** in hovers (VS Code issues #79759, #273521)
- **LaTeX Workshop workaround**: MathJax SVG → hidden webview → canvas → PNG data URI → markdown image
- Built-in `$$...$$` KaTeX works (already implemented in our extension)

### 3. Editor Decorations — Inline, limited
- `contentText`: Plain text only → Unicode approximation only
- `contentIconPath`: SVG file reference possible, but overlaps subsequent lines
- No inline HTML rendering
- Current approach (Unicode via `simpleToUnicode()`) is the practical maximum

### 4. WebviewEditorInset — Proposed API (risky)
- Inline webview in editor at specific line
- Still proposed API since 2019 (issue #85682)
- Cannot be published to marketplace without special approval
- Heavy: each inset is a full webview

---

## How Existing Extensions Do It

| Extension | Library | Surface | Approach |
|---|---|---|---|
| VS Code built-in Markdown | KaTeX (markdown-it-katex) | Markdown preview webview | KaTeX HTML+CSS in webview |
| LaTeX Workshop | MathJax | Hover tooltip | MathJax SVG → canvas → PNG data URI → MarkdownString image |
| Ultra Math Preview | MathJax/KaTeX | WebviewEditorInset (proposed) | Webview inset rendered inline |
| Markdown+Math | KaTeX | Markdown preview | markdown-it plugin |

---

## Recommendation

### Tier 1: KaTeX in Webview Panel (primary renderer)
- Upgrade `MathPreviewPanel` to use bundled KaTeX
- `renderToString()` produces styled HTML
- Bundle KaTeX CSS + fonts as extension resources
- **Best quality, most reliable, zero external deps**
- ~69 KB gzipped JS + fonts

### Tier 2: Hover Preview (already working)
- VS Code built-in `$$...$$` KaTeX rendering already works in our hover provider
- No additional library needed for hover

### Tier 3: Inline Decorations (current approach is good)
- Keep `simpleToUnicode()` for `contentText` decorations
- Optionally enhance with `unicodeit` library (299 KB) for broader LaTeX→Unicode coverage
- This is the practical maximum for inline decorations

### Feature Request: Pure Simple LaTeX Renderer
- Long-term: implement LaTeX rendering natively in Simple (compiler-side)
- `src/lib/mathjax.spl` already exists as SFFI wrapper for MathJax
- Could expose `render_latex_to_svg()` via LSP for in-process rendering
- Would eliminate JS dependency entirely for LSP-connected mode

---

## Decision Matrix

| Goal | Best Library | Why |
|---|---|---|
| Webview panel rendering | **KaTeX** | Fastest, smallest, beautiful output, zero deps |
| SVG generation (for images) | **MathJax** | Only lib with native SVG output |
| Inline decoration text | **unicodeit** or current `simpleToUnicode()` | Only Unicode works in `contentText` |
| Full LaTeX AST manipulation | **unified-latex** | Modern, small, unified.js ecosystem |
| Maximum LaTeX coverage | **MathJax** | Most complete TeX parser |
| Minimum bundle size | **Temml** | ~15-20 KB JS, but MathML-only output |

### Winner: **KaTeX** for primary rendering
- VS Code itself uses KaTeX
- Fastest rendering
- Smallest full-featured engine
- Best community support
- Works perfectly in webview panels
- Already available in VS Code hovers via `$$...$$`
