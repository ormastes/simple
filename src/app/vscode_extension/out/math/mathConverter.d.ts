/**
 * Math Expression Converter
 *
 * Converts Simple math block syntax to LaTeX and Unicode representations.
 * Used by hover provider, decoration provider, and preview panel.
 *
 * This is a lightweight TypeScript port of the core conversion logic
 * from the Simple rendering infrastructure -- sufficient for IDE display purposes.
 * The full conversion is done server-side by the LSP.
 *
 * Simple-side equivalents:
 *   simpleToLatex()   -> src/lib/math_repr.spl render_latex_raw()
 *   simpleToUnicode() -> src/lib/math_repr.spl to_pretty()
 *
 * Supporting modules in the Simple codebase:
 *   src/lib/repr.spl         - Pretty/LaTeX builders (fraction, power, sqrt, sum, integral)
 *   src/lib/unicode_math.spl - Unicode character tables (greek, superscript, subscript, math_sym)
 *   src/lib/mathjax.spl      - MathJax SFFI wrapper (SVG/HTML rendering via Node.js bridge)
 *   src/app/lsp/handlers/hover.spl - LSP hover handler using render_latex_raw() + to_pretty()
 */
export declare function simpleToLatex(source: string): string;
export declare function simpleToUnicode(source: string): string;
