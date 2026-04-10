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
exports.renderSpacerSvgFile = renderSpacerSvgFile;
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
const MATHJAX_EX_TO_EM = 0.45;
const MAX_HEIGHT_EM = 3.0;
const SVG_CACHE_VERSION = 'v2';
const SVG_SPACER_CACHE_VERSION = 'v1';
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
function exToEm(value) {
    return value * MATHJAX_EX_TO_EM;
}
function parseSvgDimension(svg, attr) {
    const match = svg.match(new RegExp(`${attr}="([\\d.]+)ex"`));
    return match ? parseFloat(match[1]) : undefined;
}
function rewriteSvgDimensions(svg, heightEm, widthEm) {
    return svg
        .replace(/height="([\d.]+)ex"/, `height="${heightEm.toFixed(3)}em"`)
        .replace(/width="([\d.]+)ex"/, `width="${widthEm.toFixed(3)}em"`);
}
/**
 * Render LaTeX to an SVG file on disk. Returns the file URI + height info.
 * Uses a content-hash cache to avoid regenerating identical expressions.
 */
function renderToSvgFile(latex, cacheDir, foregroundColor = '#cccccc') {
    const hash = crypto.createHash('md5')
        .update(`${SVG_CACHE_VERSION}:${latex}:${foregroundColor}`)
        .digest('hex')
        .slice(0, 12);
    const filePath = path.join(cacheDir, `math-${hash}.svg`);
    const metaPath = filePath + '.meta';
    // Return cached file if it exists
    if (fs.existsSync(filePath) && fs.existsSync(metaPath)) {
        const meta = JSON.parse(fs.readFileSync(metaPath, 'utf8'));
        return {
            uri: vscode.Uri.file(filePath),
            heightEm: meta.heightEm,
            descentEm: meta.descentEm,
            widthEm: meta.widthEm,
        };
    }
    let svg = latexToSvg(latex);
    if (!svg) {
        return undefined;
    }
    // Parse height and descent from the SVG
    const vaMatch = svg.match(/vertical-align:\s*-([\d.]+)ex/);
    const heightEx = parseSvgDimension(svg, 'height') ?? 1.5;
    const widthEx = parseSvgDimension(svg, 'width') ?? heightEx;
    const descentEx = vaMatch ? parseFloat(vaMatch[1]) : 0;
    let heightEm = exToEm(heightEx);
    let widthEm = exToEm(widthEx);
    let descentEm = exToEm(descentEx);
    if (heightEm > MAX_HEIGHT_EM) {
        const scale = MAX_HEIGHT_EM / heightEm;
        heightEm = MAX_HEIGHT_EM;
        widthEm = widthEm * scale;
        descentEm = descentEm * scale;
    }
    // Normalize dimensions for VSCode's em-based editor metrics and remove
    // MathJax's own baseline adjustment, which conflicts with decoration placement.
    svg = rewriteSvgDimensions(svg, heightEm, widthEm);
    svg = svg.replace(/vertical-align:\s*-[\d.]+ex;?\s*/, '');
    // Inject foreground color so SVG matches editor theme
    const colored = svg.replace(/<svg /, `<svg color="${foregroundColor}" `);
    // Ensure cache directory exists
    if (!fs.existsSync(cacheDir)) {
        fs.mkdirSync(cacheDir, { recursive: true });
    }
    fs.writeFileSync(filePath, colored, 'utf8');
    fs.writeFileSync(metaPath, JSON.stringify({ heightEm, descentEm, widthEm }), 'utf8');
    return { uri: vscode.Uri.file(filePath), heightEm, descentEm, widthEm };
}
/**
 * Render a transparent spacer SVG to disk.
 *
 * This is used as a hidden attachment so the editor line box has a real image
 * with the desired height, which works better than relying on decoration
 * attachment height alone.
 */
function renderSpacerSvgFile(cacheDir, heightEm, widthEm = 0.01) {
    const normalizedHeight = Math.max(heightEm, 0.25);
    const normalizedWidth = Math.max(widthEm, 0.01);
    const hash = crypto.createHash('md5')
        .update(`${SVG_SPACER_CACHE_VERSION}:${normalizedHeight.toFixed(3)}:${normalizedWidth.toFixed(3)}`)
        .digest('hex')
        .slice(0, 12);
    const filePath = path.join(cacheDir, `spacer-${hash}.svg`);
    const metaPath = filePath + '.meta';
    if (fs.existsSync(filePath) && fs.existsSync(metaPath)) {
        const meta = JSON.parse(fs.readFileSync(metaPath, 'utf8'));
        return {
            uri: vscode.Uri.file(filePath),
            heightEm: meta.heightEm,
            widthEm: meta.widthEm,
        };
    }
    const spacerSvg = [
        '<svg xmlns="http://www.w3.org/2000/svg"',
        ` width="${normalizedWidth.toFixed(3)}em"`,
        ` height="${normalizedHeight.toFixed(3)}em"`,
        ' viewBox="0 0 1 1"',
        ' preserveAspectRatio="none"',
        ' focusable="false"',
        ' aria-hidden="true">',
        '<rect width="100%" height="100%" fill="transparent"/>',
        '</svg>',
    ].join('');
    if (!fs.existsSync(cacheDir)) {
        fs.mkdirSync(cacheDir, { recursive: true });
    }
    fs.writeFileSync(filePath, spacerSvg, 'utf8');
    fs.writeFileSync(metaPath, JSON.stringify({ heightEm: normalizedHeight, widthEm: normalizedWidth }), 'utf8');
    return {
        uri: vscode.Uri.file(filePath),
        heightEm: normalizedHeight,
        widthEm: normalizedWidth,
    };
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