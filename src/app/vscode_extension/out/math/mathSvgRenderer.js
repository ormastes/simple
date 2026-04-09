"use strict";
/**
 * Math SVG Renderer — generates SVG images from LaTeX using MathJax.
 *
 * Used by the decoration provider to display rendered math inline in the editor
 * when the cursor is not on the math line. SVGs are cached to disk for reuse.
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.latexToSvg = latexToSvg;
exports.renderToSvgFile = renderToSvgFile;
exports.clearSvgCache = clearSvgCache;
const vscode = __importStar(require("vscode"));
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const crypto = __importStar(require("crypto"));
// MathJax components for server-side TeX → SVG rendering
const mathjax_js_1 = require("mathjax-full/js/mathjax.js");
const tex_js_1 = require("mathjax-full/js/input/tex.js");
const svg_js_1 = require("mathjax-full/js/output/svg.js");
const liteAdaptor_js_1 = require("mathjax-full/js/adaptors/liteAdaptor.js");
const html_js_1 = require("mathjax-full/js/handlers/html.js");
const AllPackages_js_1 = require("mathjax-full/js/input/tex/AllPackages.js");
let adaptor;
let mjDocument;
let initialized = false;
function ensureInitialized() {
    if (initialized) {
        return;
    }
    adaptor = (0, liteAdaptor_js_1.liteAdaptor)();
    (0, html_js_1.RegisterHTMLHandler)(adaptor);
    mjDocument = mathjax_js_1.mathjax.document('', {
        InputJax: new tex_js_1.TeX({ packages: AllPackages_js_1.AllPackages }),
        OutputJax: new svg_js_1.SVG({ fontCache: 'local' }),
    });
    initialized = true;
}
/**
 * Render a LaTeX string to an SVG string using MathJax.
 * Returns the raw SVG markup or undefined on error.
 */
function latexToSvg(latex) {
    try {
        ensureInitialized();
        const node = mjDocument.convert(latex, { display: true });
        let svg = adaptor.outerHTML(node);
        // The outerHTML wraps in <mjx-container>. Extract the inner <svg>.
        const svgMatch = svg.match(/<svg[^]*<\/svg>/);
        if (svgMatch) {
            svg = svgMatch[0];
        }
        return svg;
    }
    catch {
        return undefined;
    }
}
/**
 * Modify an SVG to be vertically centered around the text baseline.
 *
 * MathJax SVGs have: height=Hex, vertical-align=-Dex, viewBox="x0 y0 w h"
 * - Ascent above baseline: A = H - D
 * - Descent below baseline: D
 * - SVG overflow is mostly upward, making surrounding text appear at the bottom.
 *
 * Fix: extend viewBox downward and increase SVG height so the visible content
 * is vertically centered. The SVG then overflows equally above and below.
 */
function centerSvgVertically(svg) {
    const heightMatch = svg.match(/height="([\d.]+)ex"/);
    const vaMatch = svg.match(/vertical-align:\s*-([\d.]+)ex/);
    const vbMatch = svg.match(/viewBox="([\d.-]+)\s+([\d.-]+)\s+([\d.-]+)\s+([\d.-]+)"/);
    if (!heightMatch || !vaMatch || !vbMatch) {
        return svg;
    }
    const heightEx = parseFloat(heightMatch[1]);
    const descentEx = parseFloat(vaMatch[1]);
    const ascentEx = heightEx - descentEx;
    // If already roughly centered or very small, skip
    if (ascentEx - descentEx < 0.3) {
        return svg;
    }
    // VS Code contentIconPath aligns the icon bottom to the text baseline.
    // To center: add empty space at the TOP of the SVG (shift viewBox origin upward).
    // This pushes the visible content down within the SVG, so the visual center
    // aligns with the text instead of the bottom edge.
    const topPaddingEx = ascentEx - descentEx;
    const newHeightEx = heightEx + topPaddingEx;
    // Scale viewBox: shift Y origin upward by the padding amount
    const vbX = parseFloat(vbMatch[1]);
    const vbY = parseFloat(vbMatch[2]);
    const vbW = parseFloat(vbMatch[3]);
    const vbH = parseFloat(vbMatch[4]);
    const scale = vbH / heightEx;
    const topPaddingVb = topPaddingEx * scale;
    const newVbY = vbY - topPaddingVb;
    const newVbH = vbH + topPaddingVb;
    let result = svg;
    result = result.replace(/height="[\d.]+ex"/, `height="${newHeightEx.toFixed(3)}ex"`);
    result = result.replace(/viewBox="[\d.-]+\s+[\d.-]+\s+[\d.-]+\s+[\d.-]+"/, `viewBox="${vbX} ${newVbY.toFixed(1)} ${vbW} ${newVbH.toFixed(1)}"`);
    // Remove vertical-align
    result = result.replace(/vertical-align:\s*-[\d.]+ex;?\s*/, '');
    return result;
}
/**
 * Render LaTeX to an SVG file on disk. Returns the file URI.
 * Uses a content-hash cache to avoid regenerating identical expressions.
 */
function renderToSvgFile(latex, cacheDir, foregroundColor = '#cccccc') {
    const hash = crypto.createHash('md5').update(latex + foregroundColor).digest('hex').slice(0, 12);
    const filePath = path.join(cacheDir, `math-${hash}.svg`);
    // Return cached file if it exists
    if (fs.existsSync(filePath)) {
        return vscode.Uri.file(filePath);
    }
    let svg = latexToSvg(latex);
    if (!svg) {
        return undefined;
    }
    // Remove MathJax's vertical-align style (not useful for contentIconPath rendering)
    svg = svg.replace(/vertical-align:\s*-[\d.]+ex;?\s*/, '');
    // Inject foreground color so SVG matches editor theme
    const colored = svg.replace(/<svg /, `<svg color="${foregroundColor}" `);
    // Ensure cache directory exists
    if (!fs.existsSync(cacheDir)) {
        fs.mkdirSync(cacheDir, { recursive: true });
    }
    fs.writeFileSync(filePath, colored, 'utf8');
    return vscode.Uri.file(filePath);
}
/**
 * Clear the SVG cache directory.
 */
function clearSvgCache(cacheDir) {
    if (!fs.existsSync(cacheDir)) {
        return;
    }
    for (const file of fs.readdirSync(cacheDir)) {
        if (file.startsWith('math-') && file.endsWith('.svg')) {
            fs.unlinkSync(path.join(cacheDir, file));
        }
    }
}
//# sourceMappingURL=mathSvgRenderer.js.map