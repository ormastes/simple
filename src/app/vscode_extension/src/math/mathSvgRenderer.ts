/**
 * Math SVG Renderer — generates SVG images from LaTeX using MathJax.
 *
 * Used by the decoration provider to display rendered math inline in the editor
 * when the cursor is not on the math line. SVGs are cached to disk for reuse.
 */

import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import * as crypto from 'crypto';

// MathJax components for server-side TeX → SVG rendering
import { mathjax } from 'mathjax-full/js/mathjax.js';
import { TeX } from 'mathjax-full/js/input/tex.js';
import { SVG } from 'mathjax-full/js/output/svg.js';
import { liteAdaptor } from 'mathjax-full/js/adaptors/liteAdaptor.js';
import { RegisterHTMLHandler } from 'mathjax-full/js/handlers/html.js';
import { AllPackages } from 'mathjax-full/js/input/tex/AllPackages.js';

let adaptor: ReturnType<typeof liteAdaptor> | undefined;
let mjDocument: any;
let initialized = false;

function ensureInitialized(): void {
    if (initialized) { return; }
    adaptor = liteAdaptor();
    RegisterHTMLHandler(adaptor);

    mjDocument = mathjax.document('', {
        InputJax: new TeX({ packages: AllPackages }),
        OutputJax: new SVG({ fontCache: 'local' }),
    });
    initialized = true;
}

/**
 * Render a LaTeX string to an SVG string using MathJax.
 * Returns the raw SVG markup or undefined on error.
 */
export function latexToSvg(latex: string): string | undefined {
    try {
        ensureInitialized();
        const node = mjDocument.convert(latex, { display: true });
        let svg = adaptor!.outerHTML(node);

        // The outerHTML wraps in <mjx-container>. Extract the inner <svg>.
        const svgMatch = svg.match(/<svg[^]*<\/svg>/);
        if (svgMatch) {
            svg = svgMatch[0];
        }

        return svg;
    } catch {
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
function centerSvgVertically(svg: string): string {
    const heightMatch = svg.match(/height="([\d.]+)ex"/);
    const vaMatch = svg.match(/vertical-align:\s*-([\d.]+)ex/);
    const vbMatch = svg.match(/viewBox="([\d.-]+)\s+([\d.-]+)\s+([\d.-]+)\s+([\d.-]+)"/);

    if (!heightMatch || !vaMatch || !vbMatch) { return svg; }

    const heightEx = parseFloat(heightMatch[1]);
    const descentEx = parseFloat(vaMatch[1]);
    const ascentEx = heightEx - descentEx;

    // If already roughly centered or very small, skip
    if (ascentEx - descentEx < 0.3) { return svg; }

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
    result = result.replace(
        /height="[\d.]+ex"/,
        `height="${newHeightEx.toFixed(3)}ex"`
    );
    result = result.replace(
        /viewBox="[\d.-]+\s+[\d.-]+\s+[\d.-]+\s+[\d.-]+"/,
        `viewBox="${vbX} ${newVbY.toFixed(1)} ${vbW} ${newVbH.toFixed(1)}"`
    );
    // Remove vertical-align
    result = result.replace(/vertical-align:\s*-[\d.]+ex;?\s*/, '');

    return result;
}

/**
 * Render LaTeX to an SVG file on disk. Returns the file URI.
 * Uses a content-hash cache to avoid regenerating identical expressions.
 */
export function renderToSvgFile(
    latex: string,
    cacheDir: string,
    foregroundColor: string = '#cccccc',
): vscode.Uri | undefined {
    const hash = crypto.createHash('md5').update(latex + foregroundColor).digest('hex').slice(0, 12);
    const filePath = path.join(cacheDir, `math-${hash}.svg`);

    // Return cached file if it exists
    if (fs.existsSync(filePath)) {
        return vscode.Uri.file(filePath);
    }

    let svg = latexToSvg(latex);
    if (!svg) { return undefined; }

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
export function clearSvgCache(cacheDir: string): void {
    if (!fs.existsSync(cacheDir)) { return; }
    for (const file of fs.readdirSync(cacheDir)) {
        if (file.startsWith('math-') && file.endsWith('.svg')) {
            fs.unlinkSync(path.join(cacheDir, file));
        }
    }
}
