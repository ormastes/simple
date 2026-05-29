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

const MATHJAX_EX_TO_EM = 0.45;
// HEIGHT FIT PATH:
// This is a renderer-side clamp for raw MathJax output before it reaches the
// decoration provider. The provider may scale further for inline fitting.
const MAX_HEIGHT_EM = 3.0;
const SVG_CACHE_VERSION = 'v2';

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

/** Result of SVG rendering: file URI + normalized em metrics for inline fitting. */
export interface SvgRenderResult {
    uri: vscode.Uri;
    /** SVG height in em units after normalization */
    heightEm: number;
    /** Descent below baseline in em units after normalization */
    descentEm: number;
    /** SVG width in em units after normalization */
    widthEm: number;
}

function exToEm(value: number): number {
    return value * MATHJAX_EX_TO_EM;
}

function parseSvgDimension(svg: string, attr: 'height' | 'width'): number | undefined {
    const match = svg.match(new RegExp(`${attr}="([\\d.]+)ex"`));
    return match ? parseFloat(match[1]) : undefined;
}

function rewriteSvgDimensions(svg: string, heightEm: number, widthEm: number): string {
    return svg
        .replace(/height="([\d.]+)ex"/, `height="${heightEm.toFixed(3)}em"`)
        .replace(/width="([\d.]+)ex"/, `width="${widthEm.toFixed(3)}em"`);
}

/**
 * Render LaTeX to an SVG file on disk. Returns the file URI + height info.
 * Uses a content-hash cache to avoid regenerating identical expressions.
 */
export function renderToSvgFile(
    latex: string,
    cacheDir: string,
    foregroundColor: string = '#cccccc',
): SvgRenderResult | undefined {
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
    if (!svg) { return undefined; }

    // Parse height and descent from the SVG
    const vaMatch = svg.match(/vertical-align:\s*-([\d.]+)ex/);
    const heightEx = parseSvgDimension(svg, 'height') ?? 1.5;
    const widthEx = parseSvgDimension(svg, 'width') ?? heightEx;
    const descentEx = vaMatch ? parseFloat(vaMatch[1]) : 0;
    let heightEm = exToEm(heightEx);
    let widthEm = exToEm(widthEx);
    let descentEm = exToEm(descentEx);

    // HEIGHT FIT PATH:
    // Normalize oversized MathJax SVGs before the editor decoration path sees them.
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
