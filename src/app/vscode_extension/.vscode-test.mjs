import { defineConfig } from '@vscode/test-cli';

export default defineConfig([
  {
    label: 'gui',
    files: 'out/test/gui/**/*.test.js',
    version: 'stable',
    workspaceFolder: './test-workspace',
    launchArgs: [
      '--disable-gpu',
      '--disable-workspace-trust'
    ],
    mocha: {
      ui: 'tdd',
      timeout: 30000,
      color: true,
      reporter: 'spec'
    }
  }
]);
