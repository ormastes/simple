"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.detectTestBlocks = detectTestBlocks;
const DESCRIBE_RE = /^(\s*)(describe)\s+"([^"]+)":/;
const CONTEXT_RE = /^(\s*)(context)\s+"([^"]+)":/;
const IT_RE = /^(\s*)(it)\s+"([^"]+)":/;
const SDOCTEST_RE = /^\s*"""\s*sdoctest:/;
function detectTestBlocks(document) {
    const blocks = [];
    for (let line = 0; line < document.lineCount; line++) {
        const text = document.lineAt(line).text;
        let match = text.match(DESCRIBE_RE);
        if (match) {
            blocks.push({ kind: 'describe', label: match[3], line });
            continue;
        }
        match = text.match(CONTEXT_RE);
        if (match) {
            blocks.push({ kind: 'context', label: match[3], line });
            continue;
        }
        match = text.match(IT_RE);
        if (match) {
            blocks.push({ kind: 'it', label: match[3], line });
            continue;
        }
        if (SDOCTEST_RE.test(text)) {
            blocks.push({ kind: 'sdoctest', label: 'sdoctest', line });
        }
    }
    return blocks;
}
//# sourceMappingURL=testDiscovery.js.map