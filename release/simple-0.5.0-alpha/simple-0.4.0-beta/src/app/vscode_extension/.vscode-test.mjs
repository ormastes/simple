/**
 * VSCode Extension Test Configuration
 * Defines test suites and VSCode versions for testing
 */

import { defineConfig } from '@vscode/test-cli';

export default defineConfig({
  // Test files pattern
  files: 'out/test/**/*.test.js',

  // VSCode version to test against
  version: '1.80.0',

  // Test workspace
  workspaceFolder: './test-workspace',

  // Launch options
  launchArgs: [
    '--disable-extensions',  // Disable other extensions
    '--disable-gpu',         // Disable GPU for CI
    '--disable-workspace-trust'  // Trust all workspaces
  ],

  // Mocha options
  mocha: {
    ui: 'bdd',
    timeout: 20000,
    color: true,
    reporter: 'spec'
  },

  // Multiple test suites
  tests: [
    {
      // LSP e2e tests
      label: 'lsp-e2e',
      files: 'out/test/e2e/lsp/**/*.test.js',
      workspaceFolder: './test-workspace',
      mocha: {
        timeout: 30000
      }
    },
    {
      // AI features e2e tests
      label: 'ai-e2e',
      files: 'out/test/e2e/ai/**/*.test.js',
      workspaceFolder: './test-workspace',
      mocha: {
        timeout: 60000  // AI requests may take longer
      }
    },
    {
      // GUI tests (Electron)
      label: 'gui',
      files: 'out/test/gui/**/*.test.js',
      workspaceFolder: './test-workspace',
      launchArgs: [
        '--disable-workspace-trust'
        // Enable extensions for GUI tests
      ],
      mocha: {
        timeout: 30000
      }
    },
    {
      // Integration tests
      label: 'integration',
      files: 'out/test/integration/**/*.test.js',
      workspaceFolder: './test-workspace',
      mocha: {
        timeout: 20000
      }
    }
  ]
});
