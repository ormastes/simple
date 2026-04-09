/**
 * Math SVG Renderer — generates SVG images from LaTeX using MathJax.
 *
 * Used by the decoration provider to display rendered math inline in the editor
 * when the cursor is not on the math line. SVGs are cached to disk for reuse.
 */
import * as vscode from 'vscode';
/**
 * Render a LaTeX string to an SVG string using MathJax.
 * Returns the raw SVG markup or undefined on error.
 */
export declare function latexToSvg(latex: string): string | undefined;
/**
 * Render LaTeX to an SVG file on disk. Returns the file URI.
 * Uses a content-hash cache to avoid regenerating identical expressions.
 */
export declare function renderToSvgFile(latex: string, cacheDir: string, foregroundColor?: string): vscode.Uri | undefined;
/**
 * Clear the SVG cache directory.
 */
export declare function clearSvgCache(cacheDir: string): void;
