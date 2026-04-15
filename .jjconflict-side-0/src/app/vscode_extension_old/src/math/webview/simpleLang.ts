/**
 * Minimal Simple language syntax highlighting for CodeMirror 6.
 *
 * Covers keywords, strings, comments, numbers, and math blocks.
 * Not a full parser — sufficient for math-focused editing in the custom editor.
 */

import { StreamLanguage, StringStream } from '@codemirror/language';
import { tags } from '@lezer/highlight';

const KEYWORDS = new Set([
    'fn', 'class', 'struct', 'enum', 'trait', 'mixin', 'impl',
    'if', 'else', 'for', 'while', 'loop', 'match', 'return', 'break', 'continue',
    'use', 'import', 'module', 'pub', 'priv', 'mut', 'let', 'var', 'val', 'const',
    'true', 'false', 'nil', 'self', 'super', 'new', 'delete',
    'async', 'await', 'yield', 'spawn', 'try', 'catch', 'throw',
    'type', 'where', 'as', 'in', 'is', 'not', 'and', 'or',
    'extern', 'unsafe', 'static', 'inline', 'override', 'abstract',
    'test', 'spec', 'assert', 'require', 'ensure',
]);

const MATH_PREFIXES = new Set(['m', 'loss', 'nograd']);

interface SimpleState {
    inTripleString: boolean;
    inMathBlock: number; // nesting depth
}

function tokenSimple(stream: StringStream, state: SimpleState): string | null {
    // Triple-quoted string continuation
    if (state.inTripleString) {
        while (!stream.eol()) {
            if (stream.match('"""')) {
                state.inTripleString = false;
                return 'string';
            }
            stream.next();
        }
        return 'string';
    }

    // Math block content
    if (state.inMathBlock > 0) {
        while (!stream.eol()) {
            const ch = stream.peek();
            if (ch === '{') {
                state.inMathBlock++;
                stream.next();
            } else if (ch === '}') {
                state.inMathBlock--;
                stream.next();
                if (state.inMathBlock === 0) {
                    return 'atom';
                }
            } else {
                stream.next();
            }
        }
        return 'atom';
    }

    // Whitespace
    if (stream.eatSpace()) return null;

    // Comment
    if (stream.match('#')) {
        stream.skipToEnd();
        return 'comment';
    }

    // Triple-quoted string
    if (stream.match('"""')) {
        state.inTripleString = true;
        while (!stream.eol()) {
            if (stream.match('"""')) {
                state.inTripleString = false;
                return 'string';
            }
            stream.next();
        }
        return 'string';
    }

    // String
    if (stream.peek() === '"') {
        stream.next();
        let escaped = false;
        while (!stream.eol()) {
            const ch = stream.next()!;
            if (escaped) {
                escaped = false;
            } else if (ch === '\\') {
                escaped = true;
            } else if (ch === '"') {
                return 'string';
            }
        }
        return 'string';
    }

    // Number
    if (stream.match(/^0x[0-9a-fA-F_]+/) || stream.match(/^0b[01_]+/) || stream.match(/^[0-9][0-9_]*(\.[0-9_]+)?([eE][+-]?[0-9_]+)?/)) {
        return 'number';
    }

    // Math block opening: m{ / loss{ / nograd{
    const remaining = stream.string.slice(stream.pos);
    const wordMatch = remaining.match(/^[a-zA-Z_][a-zA-Z0-9_]*/);
    if (wordMatch) {
        const word = wordMatch[0];
        if (MATH_PREFIXES.has(word)) {
            // Look ahead for {
            const afterWord = remaining[word.length];
            if (afterWord === '{') {
                stream.pos += word.length + 1;
                state.inMathBlock = 1;
                return 'keyword';
            }
        }
    }

    // Identifier / keyword
    if (stream.match(/^[a-zA-Z_][a-zA-Z0-9_]*/)) {
        const word = stream.current();
        if (KEYWORDS.has(word)) return 'keyword';
        if (word[0] === word[0].toUpperCase() && word[0] !== '_') return 'type';
        return 'variable';
    }

    // Operators
    if (stream.match(/^[+\-*/%=<>!&|^~?:@.]+/)) {
        return 'operator';
    }

    // Brackets/parens
    if (stream.match(/^[()[\]{}]/)) {
        return 'bracket';
    }

    // Skip anything else
    stream.next();
    return null;
}

export const simpleLanguage = StreamLanguage.define<SimpleState>({
    name: 'simple',
    startState(): SimpleState {
        return { inTripleString: false, inMathBlock: 0 };
    },
    token: tokenSimple,
    tokenTable: {
        keyword: tags.keyword,
        type: tags.typeName,
        variable: tags.variableName,
        string: tags.string,
        number: tags.number,
        comment: tags.lineComment,
        operator: tags.operator,
        bracket: tags.bracket,
        atom: tags.atom, // math content
    },
});
