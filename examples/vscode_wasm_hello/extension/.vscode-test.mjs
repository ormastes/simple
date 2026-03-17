import { defineConfig } from '@vscode/test-cli';

export default defineConfig([
    {
        label: 'wasm-hello',
        files: 'out/test/**/*.test.js',
        version: '1.80.0',
        workspaceFolder: './test-workspace',
        mocha: {
            ui: 'bdd',
            timeout: 20000,
            color: true,
            reporter: 'spec',
        },
        launchArgs: [
            '--disable-extensions',
            '--disable-gpu',
            '--disable-workspace-trust',
        ],
    },
]);
