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
const assert = __importStar(require("assert"));
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const vscode = __importStar(require("vscode"));
const testUtils_1 = require("../helpers/testUtils");
const editorMarkers_1 = require("../../testing/editorMarkers");
const testWorkspacePanel_1 = require("../../testing/testWorkspacePanel");
suite('GUI - Test Workspace', function () {
    this.timeout(60000);
    const rootDirs = [];
    suiteSetup(async function () {
        await testUtils_1.TestUtils.activateExtension();
        const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
        if (!workspaceRoot) {
            throw new Error('No workspace folder available');
        }
        const artifactDir = path.join(workspaceRoot, 'build', 'test-artifacts', 'workspace-demo');
        fs.mkdirSync(artifactDir, { recursive: true });
        rootDirs.push(path.join(workspaceRoot, 'target'));
        const resultJson = {
            schema_version: 1,
            source_path: path.join(workspaceRoot, 'test', 'workspace-demo.spl'),
            artifact_directory: artifactDir,
            status: 'failed',
            counts: { passed: 2, failed: 1, skipped: 0, ignored: 0, duration_ms: 42 },
            error: null,
            individual_results: [],
            artifacts: {
                summary_txt: path.join(artifactDir, 'summary.txt'),
                result_json: path.join(artifactDir, 'result.json'),
                run_log: path.join(artifactDir, 'run.log'),
                output_log: path.join(artifactDir, 'output.log'),
                stdout_log: null,
                stderr_log: null,
                combined_log: null,
            },
        };
        fs.writeFileSync(path.join(artifactDir, 'result.json'), JSON.stringify(resultJson, null, 2));
    });
    teardown(async () => {
        if (testWorkspacePanel_1.TestWorkspacePanel.currentPanel) {
            testWorkspacePanel_1.TestWorkspacePanel.close();
        }
        const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
        if (workspaceRoot) {
            const artifactRoot = path.join(workspaceRoot, 'build', 'test-artifacts', 'workspace-demo');
            fs.rmSync(artifactRoot, { recursive: true, force: true });
        }
        await testUtils_1.TestUtils.closeAllEditors();
    });
    test('discovers and renders test artifacts', async () => {
        const entries = (0, testWorkspacePanel_1.discoverTestWorkspaceEntries)(vscode.workspace.workspaceFolders);
        assert.ok(entries.length > 0, 'expected at least one discovered test result');
        assert.strictEqual(entries[0].failed, 1);
        const html = (0, testWorkspacePanel_1.buildTestWorkspaceHtml)(entries);
        assert.ok(html.includes('Simple Test Workspace'));
        assert.ok(html.includes('workspace-demo.spl'));
        assert.ok(html.includes('summary-card'));
        assert.ok(html.includes('Open Latest Artifacts'));
    });
    test('opens the workspace panel command', async () => {
        await vscode.commands.executeCommand('simple.test.openWorkspace');
        assert.ok(testWorkspacePanel_1.TestWorkspacePanel.currentPanel, 'expected workspace panel to open');
    });
    test('opens the latest test artifacts command', async () => {
        await vscode.commands.executeCommand('simple.test.openLatestArtifacts');
        assert.ok(testWorkspacePanel_1.TestWorkspacePanel.currentPanel, 'expected workspace panel to open for artifacts');
    });
    test('tracks breakpoint, bookmark, and execution pointer markers', async () => {
        const doc = await testUtils_1.TestUtils.createTestFile('marker-demo.spl', `fn main(): i32 = 1
fn next(): i32 = 2`);
        const editor = testUtils_1.TestUtils.getActiveEditor();
        const manager = new editorMarkers_1.EditorMarkerManager();
        try {
            manager.toggleBreakpoint(editor);
            await testUtils_1.TestUtils.setCursorPosition(editor, 1, 0);
            manager.toggleBookmark(editor);
            manager.togglePointer(editor);
            const state = manager.getState(doc.uri);
            assert.deepStrictEqual(state.breakpoints, [0]);
            assert.deepStrictEqual(state.bookmarks, [1]);
            assert.strictEqual(state.pointerLine, 1);
        }
        finally {
            manager.dispose();
            testUtils_1.TestUtils.deleteTestFile('marker-demo.spl');
        }
    });
});
//# sourceMappingURL=testWorkspace.test.js.map
