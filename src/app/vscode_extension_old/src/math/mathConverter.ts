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
    'tanh', 'sinh', 'cosh', 'det', 'tr', 'dim', 'ker', 'sup', 'inf',
]);

// ─── Helpers ───────────────────────────────────────────────────

/**
 * Find the matching closing parenthesis for an opening paren at `start`.
 */
function findMatchingParen(s: string, start: number): number {
    let depth = 1;
    for (let i = start + 1; i < s.length; i++) {
        if (s[i] === '(') { depth++; }
        else if (s[i] === ')') { depth--; if (depth === 0) { return i; } }
    }
    return -1;
}

/**
 * Replace `name(args)` with balanced parentheses using a callback.
 * Handles nested parens correctly unlike regex `[^)]+`.
 */
function replaceBalancedCall(
    s: string,
    name: string,
    replacer: (args: string) => string,
): string {
    let result = '';
    let i = 0;
    while (i < s.length) {
        const idx = s.indexOf(name + '(', i);
        if (idx === -1) { result += s.slice(i); break; }
        // Skip if preceded by \ (already converted)
        if (idx > 0 && s[idx - 1] === '\\') {
            result += s.slice(i, idx + name.length);
            i = idx + name.length;
            continue;
        }
        // Skip if preceded by a word char (e.g., "transform" contains "log" — skip)
        if (idx > 0 && /\w/.test(s[idx - 1])) {
            result += s.slice(i, idx + name.length);
            i = idx + name.length;
            continue;
        }
        result += s.slice(i, idx);
        const openParen = idx + name.length;
        const closeParen = findMatchingParen(s, openParen);
        if (closeParen === -1) {
            result += s.slice(idx);
            break;
        }
        const args = s.slice(openParen + 1, closeParen);
        result += replacer(args);
        i = closeParen + 1;
    }
    return result;
}

/**
 * Split args at the first comma at depth 0 (not inside nested parens).
 * Returns [first, rest] or [all, ''] if no comma found.
 */
function splitAtTopLevelComma(args: string): [string, string] {
    let depth = 0;
    for (let i = 0; i < args.length; i++) {
        if (args[i] === '(') { depth++; }
        else if (args[i] === ')') { depth--; }
        else if (args[i] === ',' && depth === 0) {
            return [args.slice(0, i).trim(), args.slice(i + 1).trim()];
        }
    }
    return [args.trim(), ''];
}

// ─── simpleToLatex ─────────────────────────────────────────────

export function simpleToLatex(source: string): string {
    let result = source;

    // ── Balanced-call constructs (recursive) ──

    // frac(a, b) → \frac{a}{b}
    result = replaceBalancedCall(result, 'frac', (args) => {
        const [a, b] = splitAtTopLevelComma(args);
        if (!b) { return `\\frac{${simpleToLatex(a)}}{}`; }
        return `\\frac{${simpleToLatex(a)}}{${simpleToLatex(b)}}`;
    });

    // sqrt(...) → \sqrt{...}
    result = replaceBalancedCall(result, 'sqrt', (args) => {
        return `\\sqrt{${simpleToLatex(args)}}`;
    });

    // sum(expr) or sum(expr, i=a..b) → \sum expr or \sum_{i=a}^{b} expr
    result = replaceBalancedCall(result, 'sum', (args) => {
        const [expr, bounds] = splitAtTopLevelComma(args);
        const boundsMatch = bounds.match(/^(\w+)=(.+)\.\.(.+)$/);
        if (boundsMatch) {
            const [, v, lo, hi] = boundsMatch;
            return `\\sum_{${simpleToLatex(v)}=${simpleToLatex(lo)}}^{${simpleToLatex(hi)}} ${simpleToLatex(expr)}`;
        }
        return `\\sum ${simpleToLatex(expr)}`;
    });

    // product(expr, i=a..b) → \prod_{i=a}^{b} expr
    result = replaceBalancedCall(result, 'product', (args) => {
        const [expr, bounds] = splitAtTopLevelComma(args);
        const boundsMatch = bounds.match(/^(\w+)=(.+)\.\.(.+)$/);
        if (boundsMatch) {
            const [, v, lo, hi] = boundsMatch;
            return `\\prod_{${simpleToLatex(v)}=${simpleToLatex(lo)}}^{${simpleToLatex(hi)}} ${simpleToLatex(expr)}`;
        }
        return `\\prod ${simpleToLatex(expr)}`;
    });

    // integral(expr, x=a..b) → \int_{a}^{b} expr \, dx
    result = replaceBalancedCall(result, 'integral', (args) => {
        const [expr, bounds] = splitAtTopLevelComma(args);
        const boundsMatch = bounds.match(/^(\w+)=(.+)\.\.(.+)$/);
        if (boundsMatch) {
            const [, v, lo, hi] = boundsMatch;
            return `\\int_{${simpleToLatex(lo)}}^{${simpleToLatex(hi)}} ${simpleToLatex(expr)} \\, d${v}`;
        }
        return `\\int ${simpleToLatex(expr)}`;
    });

    // exp(...) → \exp(...)
    result = replaceBalancedCall(result, 'exp', (args) => {
        return `\\exp\\left(${simpleToLatex(args)}\\right)`;
    });

    // log(...) → \log(...)
    result = replaceBalancedCall(result, 'log', (args) => {
        return `\\log\\left(${simpleToLatex(args)}\\right)`;
    });

    // ln(...) → \ln(...)
    result = replaceBalancedCall(result, 'ln', (args) => {
        return `\\ln\\left(${simpleToLatex(args)}\\right)`;
    });

    // tanh(...) → \tanh(...)
    result = replaceBalancedCall(result, 'tanh', (args) => {
        return `\\tanh\\left(${simpleToLatex(args)}\\right)`;
    });

    // ── Decorator constructs: hat, tilde, bar, dot, abs, norm, expect ──

    result = replaceBalancedCall(result, 'hat', (args) => {
        return `\\hat{${simpleToLatex(args)}}`;
    });

    result = replaceBalancedCall(result, 'tilde', (args) => {
        return `\\tilde{${simpleToLatex(args)}}`;
    });

    result = replaceBalancedCall(result, 'bar', (args) => {
        return `\\bar{${simpleToLatex(args)}}`;
    });

    result = replaceBalancedCall(result, 'dot', (args) => {
        return `\\dot{${simpleToLatex(args)}}`;
    });

    result = replaceBalancedCall(result, 'abs', (args) => {
        return `\\left\\lvert ${simpleToLatex(args)} \\right\\rvert`;
    });

    result = replaceBalancedCall(result, 'norm', (args) => {
        return `\\left\\lVert ${simpleToLatex(args)} \\right\\rVert`;
    });

    // expect(X) → \mathbb{E}[X]
    result = replaceBalancedCall(result, 'expect', (args) => {
        return `\\mathbb{E}[${simpleToLatex(args)}]`;
    });

    // bb(R) → \mathbb{R}
    result = replaceBalancedCall(result, 'bb', (args) => {
        return `\\mathbb{${args}}`;
    });

    // cal(L) → \mathcal{L}
    result = replaceBalancedCall(result, 'cal', (args) => {
        return `\\mathcal{${args}}`;
    });

    // dd(f, x) → \frac{\partial f}{\partial x} (shorthand partial derivative)
    result = replaceBalancedCall(result, 'dd', (args) => {
        const [f, x] = splitAtTopLevelComma(args);
        return `\\frac{\\partial ${simpleToLatex(f)}}{\\partial ${simpleToLatex(x)}}`;
    });

    // softmax(z[i]) → \mathrm{softmax}(z_i)
    result = replaceBalancedCall(result, 'softmax', (args) => {
        return `\\mathrm{softmax}\\left(${simpleToLatex(args)}\\right)`;
    });

    // cases(e1, c1; e2, c2) → \begin{cases} e1 & \text{if } cond \\ ... \end{cases}
    result = replaceBalancedCall(result, 'cases', (args) => {
        const rows = args.split(';').map(row => {
            const [expr, cond] = splitAtTopLevelComma(row);
            if (cond) {
                // Convert condition as math (not text) so symbols render
                const condTrimmed = cond.trim();
                if (condTrimmed === 'otherwise') {
                    return `${simpleToLatex(expr)} & \\text{otherwise}`;
                }
                return `${simpleToLatex(expr)} & \\text{if } ${simpleToLatex(condTrimmed)}`;
            }
            return simpleToLatex(expr);
        });
        return `\\begin{cases} ${rows.join(' \\\\ ')} \\end{cases}`;
    });

    // ── Known functions (bare keyword → \keyword) ──

    for (const fn of KNOWN_FUNCTIONS) {
        if (['log', 'ln', 'exp', 'tanh'].includes(fn)) { continue; } // handled above
        const regex = new RegExp(`(?<!\\\\)\\b${fn}\\b`, 'g');
        result = result.replace(regex, `\\${fn}`);
    }

    // argmax, argmin → \arg\max, \arg\min
    result = result.replace(/(?<!\\)\bargmax\b/g, '\\arg\\max');
    result = result.replace(/(?<!\\)\bargmin\b/g, '\\arg\\min');

    // ── Greek letters (only if not already preceded by \) ──

    for (const [name, cmd] of Object.entries(GREEK_TO_LATEX)) {
        const regex = new RegExp(`(?<!\\\\)\\b${name}\\b`, 'g');
        result = result.replace(regex, cmd);
    }

    // ── Keyword operators ──

    result = result.replace(/(?<!\\)\bpartial\b/g, '\\partial');
    result = result.replace(/(?<!\\)\bnabla\b/g, '\\nabla');
    result = result.replace(/(?<!\\)\binfinity\b/g, '\\infty');

    // Relation/logic keywords
    result = result.replace(/\bmid\b/g, '\\mid');
    result = result.replace(/\bsim\b/g, '\\sim');
    result = result.replace(/\bin\b/g, '\\in');
    result = result.replace(/\bforall\b/g, '\\forall');
    result = result.replace(/\bexists\b/g, '\\exists');
    result = result.replace(/\bto\b/g, '\\to');
    result = result.replace(/\bleq\b/g, '\\leq');
    result = result.replace(/\bgeq\b/g, '\\geq');
    result = result.replace(/\bneq\b/g, '\\neq');
    result = result.replace(/\bapprox\b/g, '\\approx');

    // ── Structural transforms ──

    // x^N where N is multi-char → x^{N}
    result = result.replace(/\^(\w{2,})/g, '^{$1}');

    // x[i] subscript → x_{i}
    // Chained subscripts A[i][j] → A_{i,j} (merge into single subscript)
    result = result.replace(/(\w)\[([^\]]+)\]\[([^\]]+)\]/g, '$1_{$2,$3}');
    // Match subscript after word char or closing brace (for hat(y)[i] → \hat{y}_{i})
    result = result.replace(/(\w|\})\[([^\]]+)\]/g, '$1_{$2}');

    // Transpose: ' → ^{T}
    result = result.replace(/(\w)'/g, '$1^{T}');

    // ── Operator symbols ──

    // Matrix multiply @ → thin space (juxtaposition in LaTeX)
    result = result.replace(/\s*@\s*/g, ' ');

    // Broadcast operators: .+ .- .* ./ → LaTeX symbols
    result = result.replace(/\.\+/g, '\\oplus');
    result = result.replace(/\.\-/g, '\\ominus');
    result = result.replace(/\.\*/g, '\\odot');
    result = result.replace(/\.\//g, '\\oslash');

    // Explicit * → \cdot
    result = result.replace(/\s*\*\s*/g, ' \\cdot ');

    return result;
}

// ─── simpleToUnicode ───────────────────────────────────────────

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

    // Matrix multiply @ → ⊗
    result = result.replace(/\s*@\s*/g, '\u2297');

    // Broadcast operators: .+ .− .* ./ → ⊕ ⊖ ⊙ ⊘
    result = result.replace(/\.\+/g, '\u2295');
    result = result.replace(/\.\-/g, '\u2296');
    result = result.replace(/\.\*/g, '\u2299');
    result = result.replace(/\.\//g, '\u2298');

    // sum → ∑, product → ∏, integral → ∫
    result = result.replace(/\bsum\b/g, '\u2211');
    result = result.replace(/\bproduct\b/g, '\u220F');
    result = result.replace(/\bintegral\b/g, '\u222B');
    result = result.replace(/\binfinity\b/g, '\u221E');

    // Nabla
    result = result.replace(/\bnabla\b/g, '\u2207');

    // Decorator functions → combining characters
    result = result.replace(/\bhat\b/g, '\u0302');
    result = result.replace(/\btilde\b/g, '\u0303');
    result = result.replace(/\bbar\b/g, '\u0304');

    // Arrow/relation operators
    result = result.replace(/\bto\b/g, '\u2192');
    result = result.replace(/\bleq\b/g, '\u2264');
    result = result.replace(/\bgeq\b/g, '\u2265');
    result = result.replace(/\bneq\b/g, '\u2260');
    result = result.replace(/\bapprox\b/g, '\u2248');
    result = result.replace(/\bmid\b/g, '|');
    result = result.replace(/\bsim\b/g, '~');
    result = result.replace(/\bin\b/g, '\u2208');
    result = result.replace(/\bforall\b/g, '\u2200');
    result = result.replace(/\bexists\b/g, '\u2203');

    return result;
}
