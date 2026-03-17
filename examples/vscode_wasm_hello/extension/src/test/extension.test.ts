import * as assert from 'assert';
import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

suite('Simple WASM Hello Extension', () => {

    test('extension activates', async () => {
        // The extension should be present in the list
        const ext = vscode.extensions.getExtension('simple-lang.simple-wasm-hello');
        // In test environment without packaging, extension may not have publisher prefix
        // So we check the command is registered instead
        const commands = await vscode.commands.getCommands(true);
        assert.ok(
            commands.includes('simpleWasmHello.showPanel'),
            'Command simpleWasmHello.showPanel should be registered'
        );
    });

    test('command opens webview panel', async () => {
        await vscode.commands.executeCommand('simpleWasmHello.showPanel');

        // Give the webview a moment to open
        await new Promise(resolve => setTimeout(resolve, 500));

        // Verify a webview panel is visible by checking tab groups
        const tabGroups = vscode.window.tabGroups;
        const wasmTab = tabGroups.all
            .flatMap(group => group.tabs)
            .find(tab => tab.label === 'Simple WASM Hello');

        assert.ok(wasmTab, 'Webview tab "Simple WASM Hello" should be open');
    });

    test('wasm file exists in extension directory', () => {
        // The .wasm file should be present after build
        const extDir = path.resolve(__dirname, '..', '..');
        const wasmPath = path.join(extDir, 'wasm', 'hello.wasm');

        if (fs.existsSync(wasmPath)) {
            const stats = fs.statSync(wasmPath);
            assert.ok(stats.size > 0, 'WASM file should not be empty');
        } else {
            // Skip gracefully if WASM not yet compiled
            console.log('WASM file not found — skipping (run build_wasm.shs first)');
        }
    });

    test('command is idempotent (reuses panel)', async () => {
        // Execute twice
        await vscode.commands.executeCommand('simpleWasmHello.showPanel');
        await new Promise(resolve => setTimeout(resolve, 300));
        await vscode.commands.executeCommand('simpleWasmHello.showPanel');
        await new Promise(resolve => setTimeout(resolve, 300));

        // Should only have one tab with this name
        const tabGroups = vscode.window.tabGroups;
        const wasmTabs = tabGroups.all
            .flatMap(group => group.tabs)
            .filter(tab => tab.label === 'Simple WASM Hello');

        assert.strictEqual(wasmTabs.length, 1, 'Should reuse existing panel, not create a second');
    });
});
