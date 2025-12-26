# Electron App Testing

Automated tests for Simple language Electron applications using Playwright.

## Prerequisites

- Node.js 16+ and npm
- Simple compiler built (`cargo build`)
- Electron apps compiled to JavaScript

## Setup

```bash
cd simple/std_lib/test/electron
npm install
```

This installs Playwright and its dependencies.

## Running Tests

### All Tests (Headless)
```bash
npm test
```

### Headed Mode (See the App)
```bash
npm run test:headed
```

### Debug Mode
```bash
npm run test:debug
```

### CI Mode (with xvfb on Linux)
```bash
# On Linux CI environments
export CI=true
xvfb-run -a npm test
```

## Test Structure

```
electron/
├── package.json           # Dependencies and test scripts
├── playwright.config.js   # Playwright configuration
├── tests/                 # Test files
│   └── hello-app.test.js  # Tests for electron_hello.spl
└── README.md              # This file
```

## Writing Tests

Tests use Playwright's Electron API:

```javascript
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');

test('app launches', async () => {
    const app = await electron.launch({
        args: ['path/to/app.js']
    });

    const isReady = await app.evaluate(({ app }) => app.isReady());
    expect(isReady).toBe(true);

    await app.close();
});
```

## Testing Headless Apps

For system tray apps without windows:

```javascript
test('no windows created', async () => {
    const windows = await electronApp.windows();
    expect(windows.length).toBe(0);
});
```

## CI/CD Integration

### GitHub Actions

```yaml
name: Electron Tests
on: [push]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-node@v3

      # Setup xvfb for headless
      - name: Setup xvfb
        run: |
          sudo apt-get install -y xvfb
          Xvfb :99 -screen 0 1024x768x24 > /dev/null 2>&1 &
          echo "DISPLAY=:99" >> $GITHUB_ENV

      - run: cd simple/std_lib/test/electron && npm install
      - run: cd simple/std_lib/test/electron && npm test
```

## Test Coverage

Current tests cover:

- ✅ App lifecycle (launch, ready, quit)
- ✅ System tray creation
- ✅ Headless mode verification
- ✅ Event handling

## Troubleshooting

### "Electron executable not found"

Make sure you've built the Simple compiler and compiled the Electron app:

```bash
cargo build
./target/debug/simple electron build examples/electron_hello.spl
```

### "Cannot find module 'playwright'"

Install dependencies:

```bash
npm install
```

### Tests timeout on CI

Increase timeout in `playwright.config.js`:

```javascript
timeout: 60000,  // 60 seconds
```

## Examples

See `../examples/electron_hello.spl` for a complete hello world example.

## Resources

- [Playwright Electron API](https://playwright.dev/docs/api/class-electron)
- [Simple Electron Guide](../../../doc/plans/ELECTRON_VSCODE_WASM_PLAN.md)
