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

/** Map of Greek letter names to LaTeX commands */
const GREEK_TO_LATEX: Record<string, string> = {
    alpha: '\\alpha', beta: '\\beta', gamma: '\\gamma', delta: '\\delta',
    epsilon: '\\epsilon', zeta: '\\zeta', eta: '\\eta', theta: '\\theta',
    iota: '\\iota', kappa: '\\kappa', lambda: '\\lambda', mu: '\\mu',
    nu: '\\nu', xi: '\\xi', pi: '\\pi', rho: '\\rho',
    sigma: '\\sigma', tau: '\\tau', upsilon: '\\upsilon', phi: '\\phi',
    chi: '\\chi', psi: '\\psi', omega: '\\omega',
    Gamma: '\\Gamma', Delta: '\\Delta', Theta: '\\Theta', Lambda: '\\Lambda',
    Xi: '\\Xi', Pi: '\\Pi', Sigma: '\\Sigma', Phi: '\\Phi',
    Psi: '\\Psi', Omega: '\\Omega',
};

/** Map of Greek letter names to Unicode characters */
const GREEK_TO_UNICODE: Record<string, string> = {
    alpha: '\u03B1', beta: '\u03B2', gamma: '\u03B3', delta: '\u03B4',
    epsilon: '\u03B5', zeta: '\u03B6', eta: '\u03B7', theta: '\u03B8',
    iota: '\u03B9', kappa: '\u03BA', lambda: '\u03BB', mu: '\u03BC',
    nu: '\u03BD', xi: '\u03BE', pi: '\u03C0', rho: '\u03C1',
    sigma: '\u03C3', tau: '\u03C4', upsilon: '\u03C5', phi: '\u03C6',
    chi: '\u03C7', psi: '\u03C8', omega: '\u03C9',
    Gamma: '\u0393', Delta: '\u0394', Theta: '\u0398', Lambda: '\u039B',
    Xi: '\u039E', Pi: '\u03A0', Sigma: '\u03A3', Phi: '\u03A6',
    Psi: '\u03A8', Omega: '\u03A9',
};

/** Superscript digit map */
const SUPERSCRIPT_DIGITS: Record<string, string> = {
    '0': '\u2070', '1': '\u00B9', '2': '\u00B2', '3': '\u00B3',
    '4': '\u2074', '5': '\u2075', '6': '\u2076', '7': '\u2077',
    '8': '\u2078', '9': '\u2079', 'n': '\u207F', 'i': '\u2071',
};

/** Known math function names that get \cmd treatment in LaTeX */
const KNOWN_FUNCTIONS = new Set([
    'sin', 'cos', 'tan', 'log', 'ln', 'exp', 'min', 'max', 'lim',
]);

/**
 * Convert Simple math expression to LaTeX string.
 *
 * Handles:
 * - `^N` → `^{N}` for multi-char exponents
 * - `_N` / `[N]` subscripts → `_{N}`
 * - Greek names → `\alpha`, `\beta`, etc.
 * - `sqrt(...)` → `\sqrt{...}`
 * - `frac(a,b)` → `\frac{a}{b}`
 * - Known functions → `\sin`, `\cos`, etc.
 */
export function simpleToLatex(source: string): string {
    let result = source;

    // frac(a, b) → \frac{a}{b}
    result = result.replace(/frac\(([^,]+),\s*([^)]+)\)/g, '\\frac{$1}{$2}');

    // sqrt(...) → \sqrt{...}
    result = result.replace(/sqrt\(([^)]+)\)/g, '\\sqrt{$1}');

    // Known functions: sin(x) → \sin(x)
    for (const fn of KNOWN_FUNCTIONS) {
        const regex = new RegExp(`\\b${fn}\\b`, 'g');
        result = result.replace(regex, `\\${fn}`);
    }

    // Greek letter names → LaTeX commands (whole words only)
    for (const [name, cmd] of Object.entries(GREEK_TO_LATEX)) {
        const regex = new RegExp(`\\b${name}\\b`, 'g');
        result = result.replace(regex, cmd);
    }

    // x^N where N is multi-char → x^{N}
    result = result.replace(/\^(\w{2,})/g, '^{$1}');

    // x[i] subscript → x_{i}
    result = result.replace(/(\w)\[([^\]]+)\]/g, '$1_{$2}');

    // Transpose: ' → ^{T}
    result = result.replace(/(\w)'/g, '$1^{T}');

    // Explicit * → \cdot
    result = result.replace(/\s*\*\s*/g, ' \\cdot ');

    return result;
}

/**
 * Convert Simple math expression to Unicode pretty text.
 *
 * Handles:
 * - `^2` → `²`, `^3` → `³`, `^n` → `ⁿ`
 * - Greek names → Unicode Greek (α, β, π, etc.)
 * - `sqrt` → `√`
 * - `*` → `·`
 */
export function simpleToUnicode(source: string): string {
    let result = source;

    // Greek letter names → Unicode characters (whole words only)
    for (const [name, ch] of Object.entries(GREEK_TO_UNICODE)) {
        const regex = new RegExp(`\\b${name}\\b`, 'g');
        result = result.replace(regex, ch);
    }

    // Power with single digit/letter → superscript
    result = result.replace(/\^(\d)/g, (_match, digit) => {
        return SUPERSCRIPT_DIGITS[digit] || `^${digit}`;
    });
    result = result.replace(/\^([ni])/g, (_match, ch) => {
        return SUPERSCRIPT_DIGITS[ch] || `^${ch}`;
    });

    // sqrt → √
    result = result.replace(/\bsqrt\b/g, '\u221A');

    // Explicit * → ·
    result = result.replace(/\s*\*\s*/g, '\u00B7');

    return result;
}
