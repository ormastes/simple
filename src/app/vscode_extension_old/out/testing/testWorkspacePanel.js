"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.TestWorkspacePanel = void 0;
exports.discoverTestWorkspaceEntries = discoverTestWorkspaceEntries;
exports.buildTestWorkspaceHtml = buildTestWorkspaceHtml;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const vscode = __importStar(require("vscode"));
function discoverTestWorkspaceEntries(workspaceFolders) {
    const roots = collectArtifactRoots(workspaceFolders);
    const entries = [];
    for (const root of roots) {
        for (const resultJsonPath of walkResultJsonFiles(root)) {
            const entry = parseResultJson(resultJsonPath, root);
            if (entry) {
                entries.push(entry);
            }
        }
    }
    entries.sort((a, b) => b.updatedAt - a.updatedAt);
    return entries.slice(0, 50);
}
function buildTestWorkspaceHtml(entries) {
    const summary = summarizeEntries(entries);
    const items = entries.map((entry, index) => `
        <article class="entry" data-index="${index}">
            <div class="entry-head">
                <div>
                    <div class="entry-title">${escapeHtml(entry.label)}</div>
                    <div class="entry-path">${escapeHtml(entry.sourcePath)}</div>
                </div>
                <span class="badge ${entry.status}">${escapeHtml(entry.status)}</span>
            </div>
            <div class="entry-stats">
                <span>passed ${entry.passed}</span>
                <span>failed ${entry.failed}</span>
                <span>skipped ${entry.skipped}</span>
                <span>ignored ${entry.ignored}</span>
                <span>${entry.durationMs} ms</span>
            </div>
            <div class="entry-actions">
                <button data-action="open" data-index="${index}">Open Source</button>
                <button data-action="rerun" data-index="${index}">Rerun</button>
                <button data-action="artifacts" data-index="${index}">Open Artifacts</button>
            </div>
        </article>
    `).join('');
    const emptyState = entries.length === 0
        ? `<div class="empty">No test results found. Run <code>simple test</code> or open a workspace with artifact output.</div>`
        : '';
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; script-src 'nonce-simple';">
    <title>Simple Test Workspace</title>
    <style>
        body { font-family: var(--vscode-font-family); color: var(--vscode-foreground); background: var(--vscode-editor-background); margin: 0; padding: 16px; }
        h1 { font-size: 18px; margin: 0 0 12px; }
        .subtitle { color: var(--vscode-descriptionForeground); margin-bottom: 16px; }
        .toolbar { display: flex; flex-wrap: wrap; gap: 8px; margin-bottom: 16px; }
        .summary { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 10px; margin: 0 0 16px; }
        .summary-card { border: 1px solid var(--vscode-panel-border); border-radius: 8px; padding: 10px 12px; background: var(--vscode-sideBar-background); }
        .summary-label { color: var(--vscode-descriptionForeground); font-size: 11px; text-transform: uppercase; letter-spacing: 0.04em; }
        .summary-value { font-size: 20px; font-weight: 700; margin-top: 4px; }
        button { border: 1px solid var(--vscode-button-border, transparent); background: var(--vscode-button-background); color: var(--vscode-button-foreground); border-radius: 4px; padding: 6px 10px; cursor: pointer; }
        button:hover { background: var(--vscode-button-hoverBackground); }
        .entry { border: 1px solid var(--vscode-panel-border); border-radius: 8px; padding: 12px; margin-bottom: 12px; background: var(--vscode-sideBar-background); }
        .entry-head { display: flex; justify-content: space-between; gap: 12px; align-items: start; }
        .entry-title { font-weight: 600; margin-bottom: 4px; }
        .entry-path { color: var(--vscode-descriptionForeground); font-size: 12px; word-break: break-all; }
        .entry-stats { display: flex; flex-wrap: wrap; gap: 10px; color: var(--vscode-descriptionForeground); font-size: 12px; margin: 10px 0; }
        .entry-actions { display: flex; gap: 8px; }
        .badge { border-radius: 999px; padding: 3px 8px; font-size: 11px; font-weight: 700; text-transform: uppercase; }
        .badge.passed { background: rgba(63, 185, 80, 0.18); color: #3fb950; }
        .badge.failed { background: rgba(248, 81, 73, 0.18); color: #f85149; }
        .badge.pending { background: rgba(210, 153, 34, 0.18); color: #d29922; }
        .empty { padding: 24px; border: 1px dashed var(--vscode-panel-border); border-radius: 8px; color: var(--vscode-descriptionForeground); }
    </style>
</head>
<body>
    <h1>Simple Test Workspace</h1>
    <div class="subtitle">Structured test-runner artifacts from the current workspace</div>
    <section class="summary">
        <div class="summary-card"><div class="summary-label">Results</div><div class="summary-value">${summary.total}</div></div>
        <div class="summary-card"><div class="summary-label">Passed</div><div class="summary-value">${summary.passed}</div></div>
        <div class="summary-card"><div class="summary-label">Failed</div><div class="summary-value">${summary.failed}</div></div>
        <div class="summary-card"><div class="summary-label">Latest</div><div class="summary-value">${summary.latestLabel}</div></div>
    </section>
    <div class="toolbar">
        <button data-action="refresh">Refresh</button>
        <button data-action="open-last">Open Latest Source</button>
        <button data-action="open-last-artifacts">Open Latest Artifacts</button>
    </div>
    ${emptyState}
    ${items}
    <script nonce="simple">
        const vscode = acquireVsCodeApi();
        document.querySelectorAll('button[data-action]').forEach((button) => {
            button.addEventListener('click', () => {
                vscode.postMessage({
                    type: button.dataset.action,
                    index: button.dataset.index ? Number(button.dataset.index) : undefined,
                });
            });
        });
    </script>
</body>
</html>`;
}
class TestWorkspacePanel {
    constructor(panel, extensionUri) {
        this.disposables = [];
        this.entries = [];
        this.panel = panel;
        this.extensionUri = extensionUri;
        this.panel.webview.html = buildTestWorkspaceHtml([]);
        this.panel.webview.onDidReceiveMessage((message) => this.handleMessage(message), null, this.disposables);
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);
        this.refresh();
    }
    static show(extensionUri) {
        const column = vscode.window.activeTextEditor?.viewColumn;
        if (TestWorkspacePanel.currentPanel) {
            TestWorkspacePanel.currentPanel.panel.reveal(column);
            TestWorkspacePanel.currentPanel.refresh();
            return TestWorkspacePanel.currentPanel;
        }
        const panel = vscode.window.createWebviewPanel('simpleTestWorkspace', 'Simple Test Workspace', column || vscode.ViewColumn.Beside, {
            enableScripts: true,
            retainContextWhenHidden: true,
            localResourceRoots: [extensionUri],
        });
        TestWorkspacePanel.currentPanel = new TestWorkspacePanel(panel, extensionUri);
        return TestWorkspacePanel.currentPanel;
    }
    static isVisible() {
        return Boolean(TestWorkspacePanel.currentPanel);
    }
    static close() {
        TestWorkspacePanel.currentPanel?.panel.dispose();
        TestWorkspacePanel.currentPanel = undefined;
    }
    refresh() {
        this.entries = discoverTestWorkspaceEntries(vscode.workspace.workspaceFolders);
        this.panel.webview.html = buildTestWorkspaceHtml(this.entries);
    }
    async handleMessage(message) {
        switch (message.type) {
            case 'refresh':
                this.refresh();
                break;
            case 'open-last':
                this.openSource(this.entries[0]);
                break;
            case 'open-last-artifacts':
                this.openArtifacts(this.entries[0]);
                break;
            case 'open':
                this.openSource(this.entries[message.index]);
                break;
            case 'rerun':
                await this.rerun(this.entries[message.index]);
                break;
            case 'artifacts':
                this.openArtifacts(this.entries[message.index]);
                break;
        }
    }
    openSource(entry) {
        if (!entry?.sourcePath) {
            return;
        }
        void vscode.window.showTextDocument(vscode.Uri.file(entry.sourcePath), { preview: false });
    }
    openArtifacts(entry) {
        if (!entry?.artifactDirectory) {
            return;
        }
        void vscode.commands.executeCommand('revealFileInOS', vscode.Uri.file(entry.artifactDirectory));
    }
    async rerun(entry) {
        if (!entry?.sourcePath) {
            return;
        }
        const uri = vscode.Uri.file(entry.sourcePath);
        const isDocTest = /\.(md|markdown)$/i.test(entry.sourcePath);
        if (isDocTest) {
            await vscode.commands.executeCommand('simple.test.runSdoctest', uri);
            return;
        }
        await vscode.commands.executeCommand('simple.test.runFile', uri);
    }
    openLatestArtifacts() {
        this.openArtifacts(this.entries[0]);
    }
    dispose() {
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables.length = 0;
        this.panel.dispose();
        if (TestWorkspacePanel.currentPanel === this) {
            TestWorkspacePanel.currentPanel = undefined;
        }
    }
}
exports.TestWorkspacePanel = TestWorkspacePanel;
function collectArtifactRoots(workspaceFolders) {
    const roots = [];
    for (const folder of workspaceFolders ?? []) {
        const fsPath = folder.uri.fsPath;
        roots.push(path.join(fsPath, 'target', 'test-artifacts'));
        roots.push(path.join(fsPath, 'build', 'test-artifacts'));
    }
    return roots.filter((root) => fs.existsSync(root));
}
function walkResultJsonFiles(root) {
    const found = [];
    const stack = [root];
    while (stack.length > 0) {
        const current = stack.pop();
        let entries;
        try {
            entries = fs.readdirSync(current, { withFileTypes: true });
        }
        catch {
            continue;
        }
        for (const entry of entries) {
            const child = path.join(current, entry.name);
            if (entry.isDirectory()) {
                stack.push(child);
            }
            else if (entry.isFile() && entry.name === 'result.json') {
                found.push(child);
            }
        }
    }
    return found;
}
function parseResultJson(resultJsonPath, root) {
    try {
        const raw = fs.readFileSync(resultJsonPath, 'utf8');
        const parsed = JSON.parse(raw);
        const artifactDirectory = parsed.artifact_directory || path.dirname(resultJsonPath);
        const sourcePath = parsed.source_path || '';
        const stats = parsed.counts ?? {};
        const updatedAt = fs.statSync(resultJsonPath).mtimeMs;
        return {
            sourcePath: resolvePath(root, sourcePath),
            artifactDirectory: resolvePath(root, artifactDirectory),
            resultJsonPath,
            status: parsed.status || 'pending',
            passed: stats.passed ?? 0,
            failed: stats.failed ?? 0,
            skipped: stats.skipped ?? 0,
            ignored: stats.ignored ?? 0,
            durationMs: stats.duration_ms ?? 0,
            updatedAt,
            label: path.basename(sourcePath || artifactDirectory),
            artifactRoots: [root],
        };
    }
    catch {
        return undefined;
    }
}
function resolvePath(root, value) {
    if (!value) {
        return value;
    }
    return path.isAbsolute(value) ? value : path.join(root, value);
}
function escapeHtml(value) {
    return value
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}
function summarizeEntries(entries) {
    const summary = entries.reduce((acc, entry) => {
        acc.total += 1;
        acc.passed += entry.passed;
        acc.failed += entry.failed;
        if (!acc.latestLabel) {
            acc.latestLabel = entry.label || path.basename(entry.sourcePath || entry.artifactDirectory || 'latest');
        }
        return acc;
    }, { total: 0, passed: 0, failed: 0, latestLabel: '' });
    if (!summary.latestLabel) {
        summary.latestLabel = 'none';
    }
    return summary;
}
//# sourceMappingURL=testWorkspacePanel.js.map