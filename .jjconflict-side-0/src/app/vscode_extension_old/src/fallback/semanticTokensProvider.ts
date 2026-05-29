/**
 * Fallback Semantic Tokens Provider
 *
 * Provides semantic highlighting for .spl files when the LSP server
 * is not available. Uses regex-based tokenization matching the Simple
 * language syntax.
 */

import * as vscode from 'vscode';

/** Token legend matching package.json semanticTokenTypes */
export const TOKEN_LEGEND = new vscode.SemanticTokensLegend(
    [
        'keyword',    // 0
        'function',   // 1
        'type',       // 2
        'variable',   // 3
        'parameter',  // 4
        'property',   // 5
        'number',     // 6
        'string',     // 7
        'comment',    // 8
        'operator',   // 9
        'namespace',  // 10
    ],
    [
        'declaration',
        'definition',
        'readonly',
        'static',
        'deprecated',
        'abstract',
        'async',
        'modification',
        'documentation',
    ]
);

interface TokenMatch {
    line: number;
    startChar: number;
    length: number;
    tokenType: number;
    tokenModifiers: number;
}

const KEYWORDS = new Set([
    'if', 'else', 'elif', 'match', 'case', 'for', 'while', 'loop',
    'break', 'continue', 'return', 'fn', 'let', 'class', 'enum',
    'trait', 'impl', 'type', 'import', 'export', 'from', 'as', 'pub',
    'mut', 'iso', 'ref', 'move', 'async', 'await', 'actor',
    'effect', 'io', 'file', 'net', 'unsafe', 'var', 'val', 'me',
    'static', 'self', 'super', 'use', 'mixin', 'alias', 'in',
    'and', 'or', 'not', 'true', 'false', 'none', 'nil', 'None',
    'pass', 'pass_todo', 'pass_do_nothing', 'pass_dn',
    'describe', 'it', 'expect', 'sdoctest', 'suite', 'test',
]);

const BUILTIN_TYPES = new Set([
    'i8', 'i16', 'i32', 'i64', 'i128',
    'u8', 'u16', 'u32', 'u64', 'u128',
    'f32', 'f64', 'bool', 'String', 'char', 'void', 'never',
    'text', 'any', 'Int', 'Float', 'Bool', 'Char',
    'List', 'Map', 'Set', 'Option', 'Result', 'Array', 'Vec',
    'Tensor', 'Matrix',
]);

export class SimpleSemanticTokensProvider implements vscode.DocumentSemanticTokensProvider {
    private _onDidChangeSemanticTokens = new vscode.EventEmitter<void>();
    readonly onDidChangeSemanticTokens = this._onDidChangeSemanticTokens.event;

    provideDocumentSemanticTokens(
        document: vscode.TextDocument
    ): vscode.SemanticTokens {
        const builder = new vscode.SemanticTokensBuilder(TOKEN_LEGEND);
        const text = document.getText();
        const lines = text.split('\n');

        for (let lineNum = 0; lineNum < lines.length; lineNum++) {
            const line = lines[lineNum];
            const tokens = this.tokenizeLine(line, lineNum);
            for (const tok of tokens) {
                builder.push(tok.line, tok.startChar, tok.length, tok.tokenType, tok.tokenModifiers);
            }
        }

        return builder.build();
    }

    notifyChanged(): void {
        this._onDidChangeSemanticTokens.fire();
    }

    private tokenizeLine(line: string, lineNum: number): TokenMatch[] {
        const tokens: TokenMatch[] = [];
        // Track regions to avoid double-tokenizing
        const covered = new Set<number>();

        // 1. Comments (# to end of line)
        const commentIdx = this.findUnquotedHash(line);
        if (commentIdx >= 0) {
            tokens.push({
                line: lineNum,
                startChar: commentIdx,
                length: line.length - commentIdx,
                tokenType: 8, // comment
                tokenModifiers: 0,
            });
            for (let i = commentIdx; i < line.length; i++) covered.add(i);
        }

        // 2. Strings
        this.tokenizeStrings(line, lineNum, tokens, covered);

        // 3. Numbers
        const numRegex = /\b(0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|[0-9][0-9_]*\.?[0-9_]*(?:[eE][+-]?[0-9_]+)?)\b/g;
        let m: RegExpExecArray | null;
        while ((m = numRegex.exec(line)) !== null) {
            if (!this.isAnyCovered(m.index, m[0].length, covered)) {
                tokens.push({
                    line: lineNum,
                    startChar: m.index,
                    length: m[0].length,
                    tokenType: 6, // number
                    tokenModifiers: 0,
                });
                this.markCovered(m.index, m[0].length, covered);
            }
        }

        // 4. Word tokens: keywords, types, functions, variables
        const wordRegex = /\b([a-zA-Z_][a-zA-Z0-9_]*)\b/g;
        while ((m = wordRegex.exec(line)) !== null) {
            if (this.isAnyCovered(m.index, m[0].length, covered)) continue;

            const word = m[1];
            const afterWord = line.substring(m.index + word.length).trimStart();
            let tokenType: number;

            if (KEYWORDS.has(word)) {
                tokenType = 0; // keyword
            } else if (BUILTIN_TYPES.has(word) || /^[A-Z][a-zA-Z0-9_]*$/.test(word)) {
                tokenType = 2; // type
            } else if (afterWord.startsWith('(')) {
                tokenType = 1; // function
            } else if (this.isParameter(line, word)) {
                tokenType = 4; // parameter
            } else if (line.trimStart().startsWith('import ') || line.trimStart().startsWith('from ')) {
                tokenType = 10; // namespace
            } else {
                tokenType = 3; // variable
            }

            tokens.push({
                line: lineNum,
                startChar: m.index,
                length: word.length,
                tokenType,
                tokenModifiers: 0,
            });
            this.markCovered(m.index, word.length, covered);
        }

        // Sort by position
        tokens.sort((a, b) => a.startChar - b.startChar);
        return tokens;
    }

    private findUnquotedHash(line: string): number {
        let inString = false;
        let quote = '';
        for (let i = 0; i < line.length; i++) {
            const ch = line[i];
            if (inString) {
                if (ch === '\\') { i++; continue; }
                if (ch === quote) inString = false;
            } else {
                if (ch === '"' || ch === "'") {
                    inString = true;
                    quote = ch;
                } else if (ch === '#') {
                    return i;
                }
            }
        }
        return -1;
    }

    private tokenizeStrings(
        line: string, lineNum: number,
        tokens: TokenMatch[], covered: Set<number>
    ): void {
        let i = 0;
        while (i < line.length) {
            if (covered.has(i)) { i++; continue; }
            const ch = line[i];
            if (ch === '"' || ch === "'") {
                const start = i;
                const quote = ch;
                i++;
                while (i < line.length) {
                    if (line[i] === '\\') { i += 2; continue; }
                    if (line[i] === quote) { i++; break; }
                    i++;
                }
                tokens.push({
                    line: lineNum,
                    startChar: start,
                    length: i - start,
                    tokenType: 7, // string
                    tokenModifiers: 0,
                });
                this.markCovered(start, i - start, covered);
            } else {
                i++;
            }
        }
    }

    private isParameter(line: string, word: string): boolean {
        // Check if inside fn(... word: type ...) signature
        const fnMatch = line.match(/\bfn\s+\w+\s*\(([^)]*)\)/);
        if (fnMatch) {
            const params = fnMatch[1];
            const paramNames = params.split(',').map(p => p.trim().split(/[:\s]/)[0].trim());
            if (paramNames.includes(word)) return true;
        }
        return false;
    }

    private isAnyCovered(start: number, length: number, covered: Set<number>): boolean {
        for (let i = start; i < start + length; i++) {
            if (covered.has(i)) return true;
        }
        return false;
    }

    private markCovered(start: number, length: number, covered: Set<number>): void {
        for (let i = start; i < start + length; i++) {
            covered.add(i);
        }
    }
}
