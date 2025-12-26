# VSCode Extension Testing

Automated tests for Simple language VSCode extensions using @vscode/test-electron.

## Prerequisites

- Node.js 16+ and npm
- Simple compiler built (`cargo build`)
- VSCode extension compiled to JavaScript

## Setup

```bash
cd simple/std_lib/test/vscode
npm install
```

This installs @vscode/test-electron, Mocha, and TypeScript dependencies.

## Running Tests

### All Tests
```bash
npm test
```

This will:
1. Compile TypeScript tests (`npm run compile`)
2. Download VSCode if not already cached
3. Run tests in headless mode

### Compile Only
```bash
npm run compile
```

### Watch Mode (Auto-compile)
```bash
npm run watch
```

### CI Mode (with xvfb on Linux)
```bash
# On Linux CI environments
xvfb-run -a npm test
```

## Test Structure

```
vscode/
├── package.json                # Dependencies and test scripts
├── tsconfig.json               # TypeScript configuration
├── test/
│   ├── runTest.ts              # Test runner (downloads VSCode)
│   └── suite/
│       ├── index.ts            # Test suite loader (uses Mocha)
│       └── extension.test.ts   # Extension tests
└── README.md                   # This file
```

## Writing Tests

Tests use VSCode's API in TDD style (Mocha):

```typescript
import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Extension Test Suite', () => {
    test('Extension activates', async () => {
        const ext = vscode.extensions.getExtension('simple.hello-extension');
        await ext!.activate();
        assert.strictEqual(ext!.isActive, true);
    });

    test('Command is registered', async () => {
        const commands = await vscode.commands.getCommands(true);
        assert.ok(commands.includes('simple.hello'));
    });
});
```

## Testing Language Features

### Completion Provider
```typescript
test('Provides completions', async () => {
    const doc = await vscode.workspace.openTextDocument({
        language: 'simple',
        content: 'fn '
    });

    const completions = await vscode.commands.executeCommand<vscode.CompletionList>(
        'vscode.executeCompletionItemProvider',
        doc.uri,
        new vscode.Position(0, 3)
    );

    assert.ok(completions.items.length > 0);
});
```

### Hover Provider
```typescript
test('Shows hover information', async () => {
    const doc = await vscode.workspace.openTextDocument({
        language: 'simple',
        content: 'fn main'
    });

    const hovers = await vscode.commands.executeCommand<vscode.Hover[]>(
        'vscode.executeHoverProvider',
        doc.uri,
        new vscode.Position(0, 0)
    );

    assert.ok(hovers);
});
```

### Diagnostics
```typescript
test('Provides diagnostics', async () => {
    const doc = await vscode.workspace.openTextDocument({
        language: 'simple',
        content: 'invalid syntax'
    });

    await vscode.languages.getDiagnostics(doc.uri);
    // Check diagnostics array
});
```

## CI/CD Integration

### GitHub Actions

```yaml
name: VSCode Extension Tests
on: [push]
jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-node@v3

      - run: cargo build
      - run: cd simple/std_lib/test/vscode && npm install
      - run: cd simple/std_lib/test/vscode && npm run compile

      # Linux: xvfb for headless
      - name: Test (Linux)
        if: runner.os == 'Linux'
        run: cd simple/std_lib/test/vscode && xvfb-run -a npm test

      # macOS/Windows: native headless
      - name: Test (macOS/Windows)
        if: runner.os != 'Linux'
        run: cd simple/std_lib/test/vscode && npm test
```

## Test Coverage

Current tests cover:

- ✅ Extension activation
- ✅ Command registration
- ✅ Command execution
- ✅ Completion provider
- ✅ Hover provider
- ✅ Language configuration

## Debugging Tests

### VSCode Launch Config

Add to `.vscode/launch.json`:

```json
{
    "name": "Extension Tests",
    "type": "extensionHost",
    "request": "launch",
    "args": [
        "--extensionDevelopmentPath=${workspaceFolder}",
        "--extensionTestsPath=${workspaceFolder}/out/test/suite/index"
    ],
    "outFiles": [
        "${workspaceFolder}/out/test/**/*.js"
    ]
}
```

### Console Output

Tests print to console:

```bash
npm test 2>&1 | tee test-output.log
```

## Troubleshooting

### "Cannot find module 'vscode'"

The `vscode` module is only available when tests run inside VSCode. Don't try to import it in regular Node.js scripts.

### "Extension not found"

Make sure the extension manifest (`package.json`) has the correct extension ID and is in the `extensionDevelopmentPath`.

### Tests timeout

Increase timeout in test suite:

```typescript
test('Long running test', async function() {
    this.timeout(30000);  // 30 seconds
    // ...
});
```

### VSCode download fails

Check network connection. VSCode is downloaded to `~/.vscode-test/` on first run.

## Examples

See `../examples/vscode_hello_extension.spl` for a complete hello world extension.

## Resources

- [@vscode/test-electron Documentation](https://code.visualstudio.com/api/working-with-extensions/testing-extension)
- [VSCode Extension API](https://code.visualstudio.com/api/references/vscode-api)
- [Simple VSCode Guide](../../../doc/plans/ELECTRON_VSCODE_WASM_PLAN.md)
