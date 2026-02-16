#!/usr/bin/env node
// MathJax Bridge for Simple Language
//
// Converts LaTeX input to SVG and/or HTML output using MathJax liteAdaptor.
// Designed to be called from Simple's SFFI layer via process_run.
//
// Usage:
//   node mathjax_bridge.js --format=svg   --latex "x^{2} + 1"
//   node mathjax_bridge.js --format=html  --latex "x^{2} + 1"
//   node mathjax_bridge.js --format=both  --latex "x^{2} + 1"
//
// Output protocol (3 lines on stdout):
//   SVG:<percent-encoded-svg>
//   HTML:<percent-encoded-html>
//   ERROR:<percent-encoded-error-message>
//
// Percent-encoding avoids }} escape issues and newline problems in Simple strings.
// Exit code: 0 on success, 1 on error.

const { mathjax } = require('mathjax-full/js/mathjax.js');
const { TeX } = require('mathjax-full/js/input/tex.js');
const { SVG } = require('mathjax-full/js/output/svg.js');
const { CHTML } = require('mathjax-full/js/output/chtml.js');
const { liteAdaptor } = require('mathjax-full/js/adaptors/liteAdaptor.js');
const { RegisterHTMLHandler } = require('mathjax-full/js/handlers/html.js');
const { AllPackages } = require('mathjax-full/js/input/tex/AllPackages.js');

function percentEncode(str) {
    // Encode all non-ASCII-safe characters plus %, {, }, newlines
    let result = '';
    for (let i = 0; i < str.length; i++) {
        const ch = str[i];
        const code = str.charCodeAt(i);
        if ((code >= 0x30 && code <= 0x39) ||  // 0-9
            (code >= 0x41 && code <= 0x5A) ||  // A-Z
            (code >= 0x61 && code <= 0x7A) ||  // a-z
            ch === '-' || ch === '_' || ch === '.' || ch === '~' ||
            ch === ' ' || ch === '=' || ch === '/' || ch === ':' ||
            ch === ',' || ch === ';' || ch === '(' || ch === ')' ||
            ch === '[' || ch === ']' || ch === '!' || ch === '*' ||
            ch === '\'' || ch === '#' || ch === '?' || ch === '@') {
            result += ch;
        } else {
            // Percent-encode
            const hex = code.toString(16).toUpperCase().padStart(2, '0');
            result += '%' + hex;
        }
    }
    return result;
}

function parseArgs(argv) {
    let format = 'both';
    let latex = '';

    for (let i = 2; i < argv.length; i++) {
        const arg = argv[i];
        if (arg.startsWith('--format=')) {
            format = arg.substring('--format='.length);
        } else if (arg === '--latex' && i + 1 < argv.length) {
            latex = argv[i + 1];
            i++;
        } else if (arg.startsWith('--latex=')) {
            latex = arg.substring('--latex='.length);
        }
    }

    return { format, latex };
}

function main() {
    const { format, latex } = parseArgs(process.argv);

    if (!latex) {
        console.log('SVG:');
        console.log('HTML:');
        console.log('ERROR:' + percentEncode('No LaTeX input provided'));
        process.exit(1);
    }

    const adaptor = liteAdaptor();
    RegisterHTMLHandler(adaptor);

    const texInput = new TeX({ packages: AllPackages });

    let svgResult = '';
    let htmlResult = '';
    let errorMsg = '';

    try {
        if (format === 'svg' || format === 'both') {
            const svgOutput = new SVG({ fontCache: 'none' });
            const svgDoc = mathjax.document('', {
                InputJax: texInput,
                OutputJax: svgOutput
            });
            const svgNode = svgDoc.convert(latex, { display: true });
            svgResult = adaptor.outerHTML(svgNode);
        }

        if (format === 'html' || format === 'both') {
            const texInput2 = new TeX({ packages: AllPackages });
            const chtmlOutput = new CHTML({
                fontURL: 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/output/chtml/fonts/woff-v2'
            });
            const htmlDoc = mathjax.document('', {
                InputJax: texInput2,
                OutputJax: chtmlOutput
            });
            const htmlNode = htmlDoc.convert(latex, { display: true });
            htmlResult = adaptor.outerHTML(htmlNode);
        }
    } catch (e) {
        errorMsg = e.message || String(e);
    }

    console.log('SVG:' + percentEncode(svgResult));
    console.log('HTML:' + percentEncode(htmlResult));
    console.log('ERROR:' + (errorMsg ? percentEncode(errorMsg) : ''));

    process.exit(errorMsg ? 1 : 0);
}

main();
