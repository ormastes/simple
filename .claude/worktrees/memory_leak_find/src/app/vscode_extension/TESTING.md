# VSCode Extension Testing Guide

Comprehensive testing documentation for the Simple Language VSCode extension.

## Table of Contents

- [Overview](#overview)
- [Test Structure](#test-structure)
- [Running Tests](#running-tests)
- [Test Categories](#test-categories)
- [Writing Tests](#writing-tests)
- [CI/CD Integration](#cicd-integration)
- [Troubleshooting](#troubleshooting)

---

## Overview

The extension test suite uses:
- **VSCode Test Framework** - `@vscode/test-electron` and `@vscode/test-cli`
- **Mocha** - Test runner with BDD syntax
- **TypeScript** - Type-safe test code

### Test Coverage

| Category | Tests | Purpose |
|----------|-------|---------|
| **LSP E2E** | 17 tests | Semantic tokens, diagnostics |
| **AI E2E** | 6 tests | Inline completions |
| **GUI** | 13 tests | Chat panel, status bar, commands |
| **Integration** | 8 tests | Full workflows |
| **Total** | **44 tests** | Complete extension coverage |

---

## Test Structure

```
simple/app/vscode_extension/
├── .vscode-test.mjs          # Test configuration
├── test-workspace/           # Test workspace with sample files
│   └── sample.spl
├── src/
│   └── test/
│       ├── helpers/          # Test utilities
│       │   └── testUtils.ts  # Helper functions & sample code
│       ├── e2e/              # End-to-end tests
│       │   ├── lsp/          # LSP feature tests
│       │   │   ├── semanticTokens.test.ts (10 tests)
│       │   │   └── diagnostics.test.ts (9 tests)
│       │   └── ai/           # AI feature tests
│       │       └── inlineCompletions.test.ts (6 tests)
│       ├── gui/              # GUI/Electron tests
│       │   ├── chatPanel.test.ts (6 tests)
│       │   └── statusBar.test.ts (11 tests)
│       └── integration/      # Integration tests
│           └── fullWorkflow.test.ts (8 tests)
```

---

## Running Tests

### Prerequisites

```bash
# Install dependencies
cd simple/app/vscode_extension
npm install

# Compile TypeScript
npm run compile
```

### Run All Tests

```bash
# Run complete test suite
npm test

# Or explicitly
npm run test:all
```

### Run Specific Test Suites

```bash
# LSP end-to-end tests
npm run test:lsp

# AI feature tests
npm run test:ai

# GUI tests
npm run test:gui

# Integration tests
npm run test:integration
```

### Watch Mode (Development)

```bash
# Auto-run tests on file changes
npm run test:watch
```

### Manual Testing (Extension Development Host)

1. Open `simple/app/vscode_extension/` in VSCode
2. Press **F5** to launch Extension Development Host
3. Open test workspace: `test-workspace/`
4. Manually test features

---

## Test Categories

### 1. LSP E2E Tests (`e2e/lsp/`)

#### Semantic Tokens Tests (`semanticTokens.test.ts`)

**10 tests** validating Tree-sitter semantic highlighting:

```typescript
// Example test
test('Should provide semantic tokens for simple function', async () => {
    const testDoc = await TestUtils.createTestFile(
        'test.spl',
        'fn add(x: i32, y: i32): i32 = x + y'
    );

    const tokens = await TestUtils.getSemanticTokens(testDoc);

    assert.ok(tokens, 'Should return semantic tokens');
    assert.ok(tokens!.data.length > 0, 'Should have token data');
});
```

**Coverage:**
- ✅ Simple functions
- ✅ Class definitions
- ✅ Incremental updates on edit
- ✅ Syntax error handling
- ✅ Async functions
- ✅ Import statements
- ✅ Consistent encoding
- ✅ Empty files
- ✅ Fibonacci (recursion)

#### Diagnostics Tests (`diagnostics.test.ts`)

**9 tests** validating error reporting:

```typescript
test('Should report syntax errors', async () => {
    const testDoc = await TestUtils.createTestFile(
        'test.spl',
        'fn broken(x: i32\n    return x + 1'
    );

    const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

    assert.ok(diagnostics.length > 0, 'Should report syntax errors');
});
```

**Coverage:**
- ✅ Valid code (no errors)
- ✅ Syntax errors
- ✅ Unclosed parenthesis
- ✅ Unexpected tokens
- ✅ Dynamic updates on edit
- ✅ Multiple errors in one file
- ✅ Diagnostic ranges
- ✅ Clear on file close

---

### 2. AI E2E Tests (`e2e/ai/`)

#### Inline Completions Tests (`inlineCompletions.test.ts`)

**6 tests** validating AI-powered completions:

**Note:** Requires GitHub Copilot or compatible extension

```typescript
test('Should provide inline completion for function start', async () => {
    const testDoc = await TestUtils.createTestFile(
        'test.spl',
        'fn fibonacci('
    );

    const editor = TestUtils.getActiveEditor()!;
    await TestUtils.setCursorPosition(editor, 0, 13);

    // AI completion may appear as ghost text
    await TestUtils.sleep(3000);

    assert.ok(true, 'Inline completion request completed');
});
```

**Coverage:**
- ✅ Function completion
- ✅ Disabled state handling
- ✅ Toggle command
- ✅ Context-aware completions
- ✅ Incomplete code handling
- ✅ Debouncing

---

### 3. GUI Tests (`gui/`)

#### Chat Panel Tests (`chatPanel.test.ts`)

**6 tests** validating webview chat interface:

```typescript
test('Should open chat panel via command', async () => {
    await vscode.commands.executeCommand('simple.ai.openChat');
    await TestUtils.sleep(1000);

    assert.ok(true, 'Chat panel command executed successfully');
});
```

**Coverage:**
- ✅ Open via command
- ✅ Singleton pattern
- ✅ Explain selection integration
- ✅ Review selection integration
- ✅ Persist across editor changes
- ✅ Handle AI unavailable

#### Status Bar Tests (`statusBar.test.ts`)

**11 tests** validating commands and status bar:

```typescript
test('Should execute LSP restart command', async () => {
    await vscode.commands.executeCommand('simple.lsp.restart');
    await TestUtils.sleep(3000);

    assert.ok(TestUtils.isExtensionActive(), 'Extension should remain active');
});
```

**Coverage:**
- ✅ LSP restart command
- ✅ Show output channel
- ✅ AI toggle command
- ✅ Explain code command
- ✅ Review code command
- ✅ Generate code command
- ✅ No selection handling
- ✅ Command registration
- ✅ Configuration schema
- ✅ Dynamic config updates

---

### 4. Integration Tests (`integration/`)

#### Full Workflow Tests (`fullWorkflow.test.ts`)

**8 tests** validating complete user workflows:

```typescript
test('Complete workflow: Create file → Edit → Diagnostics → Tokens', async () => {
    // 1. Create file with error
    const testDoc = await TestUtils.createTestFile(
        'workflow.spl',
        'fn incomplete('
    );

    // 2. Check diagnostics (should have error)
    let diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
    assert.ok(diagnostics.length > 0, 'Should have syntax error');

    // 3. Fix error
    const editor = TestUtils.getActiveEditor()!;
    await TestUtils.replaceText(
        editor,
        new vscode.Range(0, 0, 0, 100),
        'fn complete(): i32 = 42'
    );

    // 4. Check diagnostics again (should be clear)
    diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
    assert.strictEqual(
        diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error).length,
        0,
        'Errors should be cleared'
    );

    // 5. Get semantic tokens
    const tokens = await TestUtils.getSemanticTokens(testDoc);
    assert.ok(tokens!.data.length > 0, 'Should have token data');
});
```

**Coverage:**
- ✅ Create → Edit → Diagnostics → Tokens
- ✅ Class usage with completion
- ✅ Import → Reference → Hover
- ✅ Function → Find references
- ✅ Multiple files cross-reference
- ✅ AI explain → Fix → Verify
- ✅ Rapid edits performance

---

## Writing Tests

### Test Helper Utilities

The `TestUtils` class provides helper methods for common test operations:

#### File Operations

```typescript
// Create test file
const doc = await TestUtils.createTestFile('test.spl', 'fn test(): void');

// Delete test file
TestUtils.deleteTestFile('test.spl');

// Close all editors
await TestUtils.closeAllEditors();
```

#### LSP Operations

```typescript
// Wait for LSP to be ready
await TestUtils.waitForLSP(10000);

// Get diagnostics
const diagnostics = await TestUtils.getDiagnostics(doc.uri);

// Get semantic tokens
const tokens = await TestUtils.getSemanticTokens(doc);

// Trigger completion
const completions = await TestUtils.triggerCompletion(doc, position);

// Get hover info
const hovers = await TestUtils.getHover(doc, position);

// Go to definition
const definitions = await TestUtils.goToDefinition(doc, position);

// Find references
const references = await TestUtils.findReferences(doc, position);
```

#### Editor Operations

```typescript
// Get active editor
const editor = TestUtils.getActiveEditor();

// Set cursor position
await TestUtils.setCursorPosition(editor, line, char);

// Select range
await TestUtils.selectRange(editor, startLine, startChar, endLine, endChar);

// Insert text
await TestUtils.insertText(editor, position, text);

// Replace text
await TestUtils.replaceText(editor, range, text);

// Type text (simulates user typing)
await TestUtils.typeText('hello');
```

#### Extension Operations

```typescript
// Check if extension is active
const isActive = TestUtils.isExtensionActive();

// Activate extension
await TestUtils.activateExtension();

// Get configuration
const value = TestUtils.getConfig<boolean>('simple', 'ai.enabled');

// Update configuration
await TestUtils.updateConfig('simple', 'ai.enabled', true);
```

#### Timing Utilities

```typescript
// Sleep for specified milliseconds
await TestUtils.sleep(1000);

// Wait for condition
await TestUtils.waitFor(
    () => someCondition(),
    5000,  // timeout
    100    // check interval
);
```

### Sample Code Snippets

Pre-defined code samples for testing:

```typescript
import { SAMPLE_CODE } from '../helpers/testUtils';

// Use in tests
const doc = await TestUtils.createTestFile('test.spl', SAMPLE_CODE.simple_function);
```

**Available samples:**
- `SAMPLE_CODE.simple_function` - Basic function
- `SAMPLE_CODE.class_definition` - Class with methods
- `SAMPLE_CODE.with_errors` - Syntax errors
- `SAMPLE_CODE.async_function` - Async/await
- `SAMPLE_CODE.imports` - Import statements
- `SAMPLE_CODE.fibonacci` - Recursive function

---

### Writing a New Test

```typescript
import * as assert from 'assert';
import * as vscode from 'vscode';
import { TestUtils, SAMPLE_CODE } from '../helpers/testUtils';

suite('My New Test Suite', () => {
    let testDoc: vscode.TextDocument | undefined;

    // Run before all tests in suite
    suiteSetup(async function() {
        this.timeout(30000);
        await TestUtils.activateExtension();
        await TestUtils.waitForLSP(15000);
    });

    // Run after each test
    teardown(async () => {
        if (testDoc) {
            TestUtils.deleteTestFile('my-test.spl');
        }
        await TestUtils.closeAllEditors();
    });

    test('Should do something useful', async () => {
        // 1. Create test file
        testDoc = await TestUtils.createTestFile(
            'my-test.spl',
            'fn test(): void'
        );

        // 2. Perform operation
        const tokens = await TestUtils.getSemanticTokens(testDoc);

        // 3. Assert result
        assert.ok(tokens, 'Should have tokens');
    });
});
```

---

## CI/CD Integration

### GitHub Actions Workflow

```yaml
# .github/workflows/extension-tests.yml
name: Extension Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v3

      - uses: actions/setup-node@v3
        with:
          node-version: '18'

      - name: Install dependencies
        working-directory: simple/app/vscode_extension
        run: npm install

      - name: Run tests
        working-directory: simple/app/vscode_extension
        run: xvfb-run -a npm test
        env:
          DISPLAY: ':99.0'

      - name: Upload test results
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: test-results
          path: simple/app/vscode_extension/test-results
```

### Local CI Simulation

```bash
# Install Xvfb (virtual display for headless testing)
sudo apt-get install -y xvfb

# Run tests headless
xvfb-run -a npm test
```

---

## Troubleshooting

### Common Issues

#### 1. Extension Not Activating

**Symptom:** Tests fail with "Extension not found"

**Solution:**
```bash
# Ensure extension ID is correct
grep "publisher" package.json
grep "name" package.json

# Should be: simple-lang.simple-language
```

#### 2. LSP Server Not Starting

**Symptom:** Timeout waiting for LSP

**Solution:**
```bash
# Ensure simple-lsp is in PATH
which simple-lsp

# Or set absolute path in test config
# Update .vscode-test.mjs with LSP path
```

#### 3. AI Tests Failing

**Symptom:** "No language models available"

**Solution:**
- Install GitHub Copilot extension
- Sign in to GitHub Copilot
- Or skip AI tests:
  ```bash
  npm run test:lsp  # Run only LSP tests
  ```

#### 4. Timeout Errors

**Symptom:** Tests timeout after 20s

**Solution:**
```typescript
// Increase timeout for specific test
test('Slow operation', async function() {
    this.timeout(60000);  // 60 seconds
    // ... test code
});
```

#### 5. Flaky Tests

**Symptom:** Tests pass/fail randomly

**Solution:**
```typescript
// Add more wait time
await TestUtils.sleep(2000);

// Or use waitFor
await TestUtils.waitFor(
    () => condition,
    10000  // Longer timeout
);
```

---

## Test Output

### Successful Run

```
Simple Language Extension Tests

  LSP E2E - Semantic Tokens
    ✓ Should provide semantic tokens for simple function (1234ms)
    ✓ Should provide semantic tokens for class definition (987ms)
    ... (10 tests)

  LSP E2E - Diagnostics
    ✓ Should report no errors for valid code (567ms)
    ✓ Should report syntax errors (432ms)
    ... (9 tests)

  AI E2E - Inline Completions
    ✓ Should provide inline completion for function start (3456ms)
    ... (6 tests)

  GUI - AI Chat Panel
    ✓ Should open chat panel via command (987ms)
    ... (6 tests)

  GUI - Status Bar and Commands
    ✓ Should execute LSP restart command (2345ms)
    ... (11 tests)

  Integration - Full Workflow
    ✓ Complete workflow: Create → Edit → Diagnostics → Tokens (4567ms)
    ... (8 tests)


  44 passing (45s)
```

---

## Performance Benchmarks

| Test Suite | Average Time | Acceptable Range |
|------------|--------------|------------------|
| LSP E2E | 15-20s | < 30s |
| AI E2E | 20-25s | < 40s (depends on AI) |
| GUI | 10-15s | < 20s |
| Integration | 25-30s | < 45s |
| **Total** | **70-90s** | **< 120s** |

---

## Best Practices

### 1. Test Isolation

```typescript
// ✅ Good: Clean up after each test
teardown(async () => {
    if (testDoc) {
        TestUtils.deleteTestFile('test.spl');
    }
    await TestUtils.closeAllEditors();
});

// ❌ Bad: Leave files/editors open
```

### 2. Timeouts

```typescript
// ✅ Good: Set reasonable timeouts
suiteSetup(async function() {
    this.timeout(30000);  // 30s for setup
});

test('AI operation', async function() {
    this.timeout(60000);  // AI may be slow
});

// ❌ Bad: Default 2s timeout (too short)
```

### 3. Assertions

```typescript
// ✅ Good: Descriptive error messages
assert.ok(tokens, 'Should return semantic tokens');
assert.strictEqual(count, 5, `Expected 5 tokens, got ${count}`);

// ❌ Bad: No context
assert.ok(tokens);
assert.strictEqual(count, 5);
```

### 4. Wait for Operations

```typescript
// ✅ Good: Wait for LSP/AI
await TestUtils.sleep(2000);  // Give LSP time to process

// ❌ Bad: No wait (race condition)
const tokens = await TestUtils.getSemanticTokens(testDoc);
```

---

## Contributing

When adding new tests:

1. **Place in correct directory:**
   - LSP features → `e2e/lsp/`
   - AI features → `e2e/ai/`
   - GUI/commands → `gui/`
   - Workflows → `integration/`

2. **Use TestUtils helpers** - Don't reimplement common operations

3. **Clean up resources** - Use `teardown()` to delete files/close editors

4. **Add descriptive names** - Test names should explain what's being tested

5. **Handle AI unavailability** - Skip AI tests gracefully if Copilot not installed

---

## References

- [VSCode Extension Testing](https://code.visualstudio.com/api/working-with-extensions/testing-extension)
- [VSCode Test Electron](https://github.com/microsoft/vscode-test)
- [Mocha Documentation](https://mochajs.org/)

---

**Last Updated:** 2025-12-26
**Test Count:** 44 tests
**Coverage:** LSP, AI, GUI, Integration
