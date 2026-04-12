import * as assert from 'assert';
import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { TestUtils } from '../helpers/testUtils';
import { EditorMarkerManager } from '../../testing/editorMarkers';
import { buildTestWorkspaceHtml, discoverTestWorkspaceEntries, TestWorkspacePanel } from '../../testing/testWorkspacePanel';

suite('GUI - Test Workspace', function() {
    this.timeout(60000);

    const rootDirs: string[] = [];

    suiteSetup(async function() {
        await TestUtils.activateExtension();

        const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
        if (!workspaceRoot) {
            throw new Error('No workspace folder available');
        }

        const artifactDir = path.join(workspaceRoot, 'target', 'test-artifacts', 'workspace-demo');
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
        if (TestWorkspacePanel.currentPanel) {
            TestWorkspacePanel.close();
        }
        const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
        if (workspaceRoot) {
            const artifactRoot = path.join(workspaceRoot, 'target', 'test-artifacts', 'workspace-demo');
            fs.rmSync(artifactRoot, { recursive: true, force: true });
        }
        await TestUtils.closeAllEditors();
    });

    test('discovers and renders test artifacts', async () => {
        const entries = discoverTestWorkspaceEntries(vscode.workspace.workspaceFolders);
        assert.ok(entries.length > 0, 'expected at least one discovered test result');
        assert.strictEqual(entries[0].failed, 1);

        const html = buildTestWorkspaceHtml(entries);
        assert.ok(html.includes('Simple Test Workspace'));
        assert.ok(html.includes('workspace-demo.spl'));
        assert.ok(html.includes('summary-card'));
        assert.ok(html.includes('Open Latest Artifacts'));
    });

    test('opens the workspace panel command', async () => {
        await vscode.commands.executeCommand('simple.test.openWorkspace');
        assert.ok(TestWorkspacePanel.currentPanel, 'expected workspace panel to open');
    });

    test('opens the latest test artifacts command', async () => {
        await vscode.commands.executeCommand('simple.test.openLatestArtifacts');
        assert.ok(TestWorkspacePanel.currentPanel, 'expected workspace panel to open for artifacts');
    });

    test('tracks breakpoint, bookmark, and execution pointer markers', async () => {
        const doc = await TestUtils.createTestFile(
            'marker-demo.spl',
            `fn main(): i32 = 1
fn next(): i32 = 2`
        );
        const editor = TestUtils.getActiveEditor()!;
        const manager = new EditorMarkerManager();

        try {
            manager.toggleBreakpoint(editor);
            await TestUtils.setCursorPosition(editor, 1, 0);
            manager.toggleBookmark(editor);
            manager.togglePointer(editor);

            const state = manager.getState(doc.uri);
            assert.deepStrictEqual(state.breakpoints, [0]);
            assert.deepStrictEqual(state.bookmarks, [1]);
            assert.strictEqual(state.pointerLine, 1);
        } finally {
            manager.dispose();
            TestUtils.deleteTestFile('marker-demo.spl');
        }
    });
});
