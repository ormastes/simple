# VS Code Math Block Inline SVG Rendering

**Status:** In Progress (height fix pending)
**Date:** 2026-04-09
**Scope:** VS Code extension math block decoration system

---

## Overview

The VS Code extension renders math blocks (`m{}`, `loss{}`, `nograd{}`) in `.spl` files as inline SVG equations. When the cursor is on a math line, raw source is shown; when the cursor moves away, the rendered equation replaces it. This document covers the current state, architecture, and remaining work.

---

## Architecture

```
User types: val ce = loss{ -frac(1,n) * sum(y[i] * log(p[i]), i=1..n) }
                │
                ▼
┌─────────────────────────────────────────┐
│  mathConverter.ts                        │
│  simpleToLatex() — DSL → LaTeX string   │
│  simpleToUnicode() — DSL → Unicode text │
│  • Balanced-paren parser (recursive)     │
│  • 30+ construct handlers               │
└───────────────┬─────────────────────────┘
                │ LaTeX string
                ▼
┌─────────────────────────────────────────┐
│  mathSvgRenderer.ts                      │
│  latexToSvg() — MathJax liteAdaptor     │
│  renderToSvgFile() — SVG file on disk   │
│  • Content-hash disk cache (.svg+.meta) │
│  • Height/descent metadata              │
└───────────────┬─────────────────────────┘
                │ SvgRenderResult {uri, heightEx, descentEx}
                ▼
┌─────────────────────────────────────────┐
│  mathDecorationProvider.ts               │
│  • Cursor-aware reveal (raw vs SVG)      │
│  • contentIconPath decoration            │
│  • Block indicators: m{} = none,         │
│    loss{} = L, nograd{} = ∅              │
│  • ⚠ Height/vertical position BROKEN    │
└─────────────────────────────────────────┘

Parallel path (Preview Panel):
┌─────────────────────────────────────────┐
│  mathPreviewPanel.ts                     │
│  KaTeX renderToString() in webview       │
│  • Full HTML/CSS rendering (works fine)  │
└─────────────────────────────────────────┘
```

---

## Current State

### Complete

| Feature | File | Status |
|---------|------|--------|
| KaTeX webview preview panel | `mathPreviewPanel.ts` | Done |
| MathJax SVG generation + disk cache | `mathSvgRenderer.ts` | Done |
| Cursor-aware reveal (raw source ↔ SVG) | `mathDecorationProvider.ts` | Done |
| Block indicators: m{}=none, loss{}=L, nograd{}=∅ | `mathDecorationProvider.ts` | Done |
| Balanced-paren parser for nested expressions | `mathConverter.ts` | Done |
| Negative lookbehind `(?<!\\)` anti-double-convert | `mathConverter.ts` | Done |
| Chained subscripts `A[i][j]` → `A_{i,j}` | `mathConverter.ts` | Done |
| `@` → thin space, `.*` → `\odot` | `mathConverter.ts` | Done |
| Sum/product/integral with limits syntax | `mathConverter.ts` | Done |
| DL constructs: hat, tilde, bar, dot, abs, norm | `mathConverter.ts` | Done |
| DL constructs: expect, bb, cal, dd, softmax, cases | `mathConverter.ts` | Done |
| Keywords: nabla, mid, sim, in, forall, exists, argmax, argmin | `mathConverter.ts` | Done |
| Relation keywords: leq, geq, neq, approx, to | `mathConverter.ts` | Done |
| DL demo file (20 equations) | `test-workspace/math_dl_demo.spl` | Done |
| Tests (50/50 passing) | `src/test/gui/mathRendering.test.ts` | Done |
| Config: `simple.math.alignment` (center/bottom) | `package.json` | Done |

### Broken: SVG Height / Vertical Positioning

**Symptom:** Inline SVG math equations render at incorrect vertical positions. Tall equations (fractions, sums with limits) are misaligned relative to surrounding code text.

**Current code** (`mathDecorationProvider.ts` lines 303-323):
```typescript
// Heuristic that doesn't work correctly
const ascent = svgResult.heightEx - svgResult.descentEx;
const shiftEm = Math.max(0, (ascent - 1) * 0.35);
const marginBottom = shiftEm > 0 ? `-${shiftEm.toFixed(2)}em` : '0';

svgDecorations.push({
    range: block.fullRange,
    renderOptions: {
        before: {
            contentIconPath: svgResult.uri,
            margin: `0 4px ${marginBottom} 0`,
            textDecoration: 'none; vertical-align: middle',
        },
    },
});
```

**Root causes (3 interacting issues):**

1. **Unit mismatch** — MathJax SVGs use `ex` units from its internal font metrics. VS Code's editor uses `em`/`px` based on the editor font. MathJax's `1ex` != editor CSS `1ex`.

2. **Dual positioning conflict** — The code applies both `vertical-align: middle` (CSS) AND `margin-bottom` offset simultaneously. These two positioning mechanisms fight each other.

3. **No per-line variable height in VS Code** — `contentIconPath` renders an `<img>` with fixed dimensions. When the SVG is taller than the line height, it overflows/clips. Monaco PR #239601 added per-line variable height internally but it is NOT exposed to the extension API.

**MathJax measured output for reference:**

| Expression | heightEx | descentEx | ascent(ex) | Current shift |
|-----------|---------|----------|-----------|--------------|
| `x^2 + 1` | 4.588 | 1.552 | 3.04 | 0.71em |
| `\frac{x}{\sqrt{1+x^2}}` | 4.837 | 2.308 | 2.53 | 0.54em |
| `\frac{\frac{1}{2}}{\frac{3}{4}}` | 6.423 | 2.645 | 3.78 | 0.97em |
| `\sum_{i=1}^{n} x_i` | 6.354 | 2.819 | 3.54 | 0.89em |
| `x + y` | 1.783 | 0.464 | 1.32 | 0.11em |

---

## Height Fix Plan

### Step 1: Convert SVG dimensions from `ex` to `em`

MathJax outputs `height="4.588ex"`. The `ex` is MathJax's internal metric, not the editor's. Convert to `em` so the SVG scales with the editor font.

**Conversion factor:** `1 MathJax-ex ≈ 0.45 em` (empirical: MathJax x-height is ~45% of CSS font-size).

In `renderToSvgFile()`, before writing SVG to disk:
- Replace `height="X.XXex"` with `height="Y.YYem"` (Y = X * 0.45)
- Replace `width="X.XXex"` with `width="Y.YYem"`
- Store converted em values in `.meta` alongside original ex values

Update `SvgRenderResult`:
```typescript
export interface SvgRenderResult {
    uri: vscode.Uri;
    heightEx: number;
    descentEx: number;
    heightEm: number;   // new: for CSS positioning
    descentEm: number;  // new: for CSS positioning
}
```

### Step 2: Remove dual positioning — use single `vertical-align`

Remove the `margin-bottom` hack. Use only `vertical-align`:

- **Center mode** (`simple.math.alignment = "center"`): `vertical-align: middle`
- **Bottom/baseline mode** (`simple.math.alignment = "bottom"`): `vertical-align: -${descentEm}em` — aligns math baseline with text baseline

### Step 3: Clamp max SVG height

For very tall expressions (nested fracs), cap height to prevent massive overflow:
```typescript
const MAX_HEIGHT_EM = 3.0; // ~3 lines of text
if (heightEm > MAX_HEIGHT_EM) {
    const scale = MAX_HEIGHT_EM / heightEm;
    heightEm = MAX_HEIGHT_EM;
    widthEm *= scale;
}
```

### Step 4: Remove lineAlignDecorationType

The `lineAlignDecorationType` was a hack to vertically center non-math text on SVG lines. Once SVG dimensions are correct in `em` units, this is unnecessary. Remove it.

---

## Files

| File | Role | Lines |
|------|------|-------|
| `src/math/mathConverter.ts` | DSL → LaTeX/Unicode conversion | ~400 |
| `src/math/mathSvgRenderer.ts` | MathJax SVG rendering + disk cache | ~120 |
| `src/math/mathDecorationProvider.ts` | VS Code decoration provider | ~475 |
| `src/math/mathPreviewPanel.ts` | KaTeX webview preview panel | ~200 |
| `src/math/index.ts` | Module activation, cache setup | ~50 |
| `test-workspace/math_dl_demo.spl` | 20 DL equation demos | 81 |
| `test-workspace/math_complex_demo.spl` | Nested expression demos | ~50 |
| `src/test/gui/mathRendering.test.ts` | Unit tests | ~200 |

### Files to modify for height fix

| File | Change |
|------|--------|
| `src/math/mathSvgRenderer.ts` | Add ex→em conversion, clamp height, rewrite SVG width/height attrs, update SvgRenderResult |
| `src/math/mathDecorationProvider.ts` | Remove margin-bottom hack, remove lineAlignDecorationType, use descentEm for baseline align |

---

## Supported Math Constructs

### Balanced-call constructs (recursive, handles nesting)

| DSL Syntax | LaTeX Output | Category |
|-----------|-------------|----------|
| `frac(a, b)` | `\frac{a}{b}` | Structure |
| `sqrt(x)` | `\sqrt{x}` | Structure |
| `sum(expr, i=a..b)` | `\sum_{i=a}^{b} expr` | Limits |
| `product(expr, i=a..b)` | `\prod_{i=a}^{b} expr` | Limits |
| `integral(expr, x=a..b)` | `\int_{a}^{b} expr \, dx` | Limits |
| `exp(x)` | `\exp(x)` | Function |
| `log(x)` | `\log(x)` | Function |
| `ln(x)` | `\ln(x)` | Function |
| `tanh(x)` | `\tanh(x)` | Function |
| `hat(x)` | `\hat{x}` | Decorator |
| `tilde(x)` | `\tilde{x}` | Decorator |
| `bar(x)` | `\bar{x}` | Decorator |
| `dot(x)` | `\dot{x}` | Decorator |
| `abs(x)` | `\lvert x \rvert` | Delimiter |
| `norm(x)` | `\lVert x \rVert` | Delimiter |
| `expect(X)` | `\mathbb{E}[X]` | Notation |
| `bb(R)` | `\mathbb{R}` | Font |
| `cal(L)` | `\mathcal{L}` | Font |
| `dd(f, x)` | `\frac{\partial f}{\partial x}` | Calculus |
| `softmax(z)` | `\mathrm{softmax}(z)` | ML |
| `cases(e1,c1; e2,c2)` | `\begin{cases}...\end{cases}` | Piecewise |

### Keyword constructs

| DSL | LaTeX | DSL | LaTeX |
|-----|-------|-----|-------|
| `nabla` | `\nabla` | `mid` | `\mid` |
| `sim` | `\sim` | `in` | `\in` |
| `forall` | `\forall` | `exists` | `\exists` |
| `argmax` | `\arg\max` | `argmin` | `\arg\min` |
| `leq` | `\leq` | `geq` | `\geq` |
| `neq` | `\neq` | `approx` | `\approx` |
| `to` | `\to` | `partial` | `\partial` |
| `infinity` | `\infty` | | |

### Operators

| DSL | LaTeX | Description |
|-----|-------|-------------|
| `@` | thin space | Matrix multiply |
| `.*` | `\odot` | Broadcast multiply |
| `.+` | `\oplus` | Broadcast add |
| `.-` | `\ominus` | Broadcast subtract |
| `./` | `\oslash` | Broadcast divide |
| `*` | `\cdot` | Scalar multiply |
| `^N` | `^{N}` | Superscript |
| `x[i]` | `x_{i}` | Subscript |
| `A[i][j]` | `A_{i,j}` | Chained subscript |
| `x'` | `x^{T}` | Transpose |

---

## Dependencies

| Package | Version | Purpose |
|---------|---------|---------|
| `mathjax-full` | ^3.2.1 | SVG generation via liteAdaptor (server-side) |
| `katex` | ^0.16.45 | HTML rendering for webview preview panel |

---

## Verification Checklist (after height fix)

1. [ ] `x + y` renders at same visual height as surrounding text
2. [ ] `\frac{1}{2}` renders centered, slightly taller than text
3. [ ] Nested fracs render without excessive overflow
4. [ ] `center` vs `bottom` alignment config setting works
5. [ ] Editor font size change causes SVG to scale proportionally
6. [ ] Dark/light theme foreground color works
7. [ ] SVG cache invalidated when conversion logic changes
8. [ ] All 50 tests pass
9. [ ] `math_dl_demo.spl` — all 20 equations render correctly

---

## Related Documents

- `doc/03_plan/simple_math_implementation.md` — Language-level math/tensor system (separate)
- `doc/03_plan/VSCODE_LSP_SEMANTIC_TOKENS_PLAN.md` — VS Code LSP integration
