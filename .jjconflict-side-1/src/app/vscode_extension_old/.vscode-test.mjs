/**
 * VSCode Extension Test Configuration
 * Defines test suites and VSCode versions for testing
 */

import { defineConfig } from '@vscode/test-cli';

const shared = {
  version: '1.82.0',
  workspaceFolder: './test-workspace',
  launchArgs: [
    '--disable-extensions',
    '--disable-gpu',
    '--disable-workspace-trust'
  ],
  mocha: {
    ui: 'tdd',
    timeout: 20000,
    color: true,
    reporter: 'spec'
  }
};

export default defineConfig([
  {
    label: 'lsp-e2e',
    files: 'out/test/e2e/lsp/**/*.test.js',
    ...shared,
    mocha: { ...shared.mocha, timeout: 30000 }
  },
  {
    label: 'ai-e2e',
    files: 'out/test/e2e/ai/**/*.test.js',
    ...shared,
    mocha: { ...shared.mocha, timeout: 60000 }
  },
  {
    label: 'gui',
    files: 'out/test/gui/**/*.test.js',
    ...shared,
    launchArgs: ['--disable-workspace-trust'],
    mocha: { ...shared.mocha, timeout: 30000 }
  },
  {
    label: 'integration',
    files: 'out/test/integration/**/*.test.js',
    ...shared,
  }
]);
