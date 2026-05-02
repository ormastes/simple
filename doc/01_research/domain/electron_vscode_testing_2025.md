# Electron & VSCode GUI Testing - Research & Best Practices (2025)

**Date:** 2025-12-26
**Purpose:** Research current best practices for testing Electron apps and VSCode extensions

## Electron App Testing

### 1. Playwright for Electron (RECOMMENDED) ✅

**Status:** Active, Microsoft-maintained
**Replaced:** Spectron (deprecated in 2021)

**Why Playwright:**
- ✅ Modern, actively maintained by Microsoft
- ✅ Cross-platform (Windows, macOS, Linux)
- ✅ Headless support out of the box
- ✅ Fast and reliable
- ✅ Great API for automation
- ✅ Supports screenshots, video recording
- ✅ Parallel test execution

**Installation:**
```bash
npm install --save-dev playwright @playwright/test
```

**Example Test:**
```javascript
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');

test('Electron app launches and shows tray', async () => {
    // Launch Electron app
    const electronApp = await electron.launch({
        args: ['dist/main.js']
    });

    // Wait for app to be ready
    const isReady = await electronApp.evaluate(async ({ app }) => {
        return app.whenReady().then(() => true);
    });
    expect(isReady).toBe(true);

    // Get first window (if any)
    const window = await electronApp.firstWindow();

    // Interact with app
    const title = await window.title();
    expect(title).toContain('System Monitor');

    // Test tray
    const trayExists = await electronApp.evaluate(({ app }) => {
        return app.isReady();
    });
    expect(trayExists).toBe(true);

    // Cleanup
    await electronApp.close();
});
```

**Headless Mode:**
```javascript
test('Headless electron test', async () => {
    const electronApp = await electron.launch({
        args: ['dist/main.js'],
        env: { ...process.env, DISPLAY: ':99' }  // For Linux CI
    });

    // Tests run without visible window
    await electronApp.close();
});
```

**CI/CD (GitHub Actions):**
```yaml
name: Electron Tests
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

      # Linux: Setup virtual display
      - name: Setup xvfb (Linux)
        if: runner.os == 'Linux'
        run: |
          sudo apt-get install -y xvfb
          Xvfb :99 -screen 0 1024x768x24 > /dev/null 2>&1 &
          echo "DISPLAY=:99" >> $GITHUB_ENV

      - run: npm install
      - run: npm test
```

---

### 2. WebdriverIO (Alternative)

**Status:** Active, community-maintained

**Why WebdriverIO:**
- ✅ Mature ecosystem
- ✅ Good documentation
- ✅ Plugin system
- ⚠️ More complex setup than Playwright

**Installation:**
```bash
npm install --save-dev webdriverio @wdio/cli
```

**Example:**
```javascript
const { remote } = require('webdriverio');

describe('Electron App', () => {
    let client;

    beforeAll(async () => {
        client = await remote({
            capabilities: {
                browserName: 'chrome',
                'goog:chromeOptions': {
                    binary: '/path/to/electron',
                    args: ['app/main.js']
                }
            }
        });
    });

    it('should launch app', async () => {
        const title = await client.getTitle();
        expect(title).toContain('App');
    });
});
```

---

### 3. Rust Options for Electron Testing

#### Option A: Use Rust to call Playwright via FFI

**Crate:** `playwright` (unofficial Rust bindings)

```toml
[dev-dependencies]
playwright = "0.0.x"
```

```rust
use playwright::Playwright;

#[tokio::test]
async fn test_electron_app() {
    let playwright = Playwright::initialize().await.unwrap();
    let electron = playwright.electron();

    let app = electron.launch(LaunchOptions {
        args: vec!["dist/main.js"],
        ..Default::default()
    }).await.unwrap();

    // Test app
    assert!(app.is_ready().await.unwrap());

    app.close().await.unwrap();
}
```

**Status:** ⚠️ Unofficial, limited features

#### Option B: Use headless-chrome Rust crate

**Crate:** `headless_chrome`

```rust
use headless_chrome::{Browser, LaunchOptions};

#[test]
fn test_electron_with_chrome() {
    let browser = Browser::new(LaunchOptions {
        headless: true,
        ..Default::default()
    }).unwrap();

    let tab = browser.new_tab().unwrap();
    // Connect to Electron's renderer process
}
```

**Status:** ⚠️ Requires custom Electron setup

#### Option C: WebDriver with fantoccini

**Crate:** `fantoccini` (WebDriver client)

```rust
use fantoccini::{Client, ClientBuilder};

#[tokio::test]
async fn test_electron() {
    let client = ClientBuilder::native()
        .connect("http://localhost:4444")
        .await
        .unwrap();

    // Selenium WebDriver talking to Electron
    client.goto("app://index.html").await.unwrap();
}
```

**Status:** ⚠️ Requires chromedriver + Electron setup

**Recommendation for Rust:** ❌ **Not recommended** - JavaScript/TypeScript with Playwright is much better supported for Electron testing.

---

## VSCode Extension Testing

### 1. @vscode/test-electron (OFFICIAL) ✅

**Status:** Official Microsoft tool
**Purpose:** API/Integration testing

**Why @vscode/test-electron:**
- ✅ Official VSCode testing framework
- ✅ Downloads VSCode automatically
- ✅ Runs in headless mode
- ✅ Perfect for API testing
- ✅ CI/CD friendly

**Installation:**
```bash
npm install --save-dev @vscode/test-electron @types/mocha mocha
```

**Test Structure:**
```
extension/
├── src/
│   └── extension.ts
├── out/
│   └── (compiled JS)
└── test/
    ├── runTest.ts          # Test runner
    └── suite/
        ├── index.ts        # Suite loader
        └── extension.test.ts  # Tests
```

**`test/runTest.ts`:**
```typescript
import * as path from 'path';
import { runTests } from '@vscode/test-electron';

async function main() {
    const extensionDevelopmentPath = path.resolve(__dirname, '../../');
    const extensionTestsPath = path.resolve(__dirname, './suite/index');

    try {
        await runTests({
            extensionDevelopmentPath,
            extensionTestsPath,
            launchArgs: [
                '--disable-extensions',
                '--disable-gpu'
            ]
        });
    } catch (err) {
        console.error('Tests failed');
        process.exit(1);
    }
}

main();
```

**`test/suite/index.ts`:**
```typescript
import * as path from 'path';
import Mocha from 'mocha';
import { glob } from 'glob';

export function run(): Promise<void> {
    const mocha = new Mocha({ ui: 'tdd', color: true });

    const testsRoot = path.resolve(__dirname, '..');

    return new Promise((resolve, reject) => {
        glob('**/**.test.js', { cwd: testsRoot }).then(files => {
            files.forEach(f => mocha.addFile(path.resolve(testsRoot, f)));

            mocha.run(failures => {
                if (failures > 0) {
                    reject(new Error(`${failures} tests failed.`));
                } else {
                    resolve();
                }
            });
        });
    });
}
```

**`test/suite/extension.test.ts`:**
```typescript
import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Extension Test Suite', () => {
    test('Extension loads', async () => {
        const ext = vscode.extensions.getExtension('publisher.extension-id');
        assert.ok(ext);

        await ext!.activate();
        assert.ok(ext!.isActive);
    });

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

        assert.ok(completions);
        assert.ok(completions.items.length > 0);
    });
});
```

**CI/CD:**
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

      - run: npm install
      - run: npm run compile

      # Linux: xvfb for headless
      - name: Test (Linux)
        if: runner.os == 'Linux'
        run: xvfb-run -a npm test

      - name: Test (macOS/Windows)
        if: runner.os != 'Linux'
        run: npm test
```

---

### 2. vscode-extension-tester (UI TESTING) ✅

**Status:** Community tool (Red Hat)
**Purpose:** UI/E2E testing

**Why Extension Tester:**
- ✅ Tests actual UI interactions
- ✅ Page Object Model for VSCode
- ✅ Selenium WebDriver based
- ✅ Can test menus, buttons, editors

**Installation:**
```bash
npm install --save-dev vscode-extension-tester
```

**Example:**
```typescript
import { VSBrowser, WebDriver } from 'vscode-extension-tester';

describe('UI Tests', () => {
    let driver: WebDriver;

    before(async function() {
        this.timeout(30000);
        driver = VSBrowser.instance.driver;
    });

    it('Opens command palette', async () => {
        const workbench = await browser.openCommandPalette();
        const input = await workbench.getQuickOpenBox();
        await input.setText('Simple: Format');
        await input.confirm();
    });

    it('Shows completion in editor', async () => {
        const editor = await workbench.getActiveEditor();
        await editor.typeText('fn ');

        // Wait for completion widget
        await driver.wait(async () => {
            const suggestions = await driver.findElements(
                By.className('monaco-list-row')
            );
            return suggestions.length > 0;
        }, 5000);
    });
});
```

---

### 3. Rust Options for VSCode Extension Testing

#### Option A: Call @vscode/test-electron via Node

**Approach:** Use Rust to orchestrate, delegate to Node.js

```rust
use std::process::Command;

#[test]
fn test_vscode_extension() {
    let output = Command::new("npm")
        .arg("test")
        .current_dir("extension/")
        .output()
        .expect("Failed to run tests");

    assert!(output.status.success());
}
```

**Status:** ✅ Works, but just wraps JavaScript tests

#### Option B: WebDriver in Rust

**Crate:** `fantoccini` + `geckodriver` or `chromedriver`

```rust
use fantoccini::{Client, ClientBuilder};

#[tokio::test]
async fn test_vscode_ui() {
    let client = ClientBuilder::native()
        .connect("http://localhost:4444")
        .await
        .unwrap();

    // This would require VSCode to be running with WebDriver
    // Not practical for extension testing
}
```

**Status:** ❌ Not practical - VSCode Extension API is JavaScript-specific

**Recommendation for Rust:** ❌ **Not recommended** - TypeScript is the right choice for VSCode extension testing.

---

## Summary & Recommendations

### For Electron Apps

**Recommended Stack:**
1. **Playwright for Electron** (JavaScript/TypeScript)
   - Modern, actively maintained
   - Excellent headless support
   - Best CI/CD integration

2. **Test Framework:** @playwright/test or Jest
3. **Language:** JavaScript/TypeScript (not Rust)

**Why not Rust?**
- ❌ No mature Rust bindings for Electron testing
- ❌ Playwright Rust bindings are unofficial/incomplete
- ❌ JavaScript is the native language for Electron

---

### For VSCode Extensions

**Recommended Stack:**
1. **API Testing:** `@vscode/test-electron` (TypeScript)
   - Official Microsoft tool
   - Perfect for testing language features

2. **UI Testing:** `vscode-extension-tester` (TypeScript)
   - For testing UI interactions
   - Selenium-based

3. **Language:** TypeScript (not Rust)

**Why not Rust?**
- ❌ VSCode Extension API is JavaScript/TypeScript only
- ❌ No Rust bindings for VSCode Extension API
- ❌ Tests must run inside VSCode's JavaScript runtime

---

## Implementation Plan for Simple

### Electron Testing (JavaScript)

**File:** `simple/std_lib/test/electron/hello-app.test.js`

```javascript
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');
const path = require('path');

test('Hello Electron App', async () => {
    const appPath = path.join(__dirname, '../examples/electron_hello.js');

    const app = await electron.launch({
        args: [appPath]
    });

    // Test app launched
    const isReady = await app.evaluate(({ app }) => app.isReady());
    expect(isReady).toBe(true);

    // Test tray exists
    const hasTray = await app.evaluate(() => {
        const { app } = require('electron');
        return app.isReady();
    });
    expect(hasTray).toBe(true);

    await app.close();
});
```

---

### VSCode Testing (TypeScript)

**File:** `simple/std_lib/test/vscode/hello-extension.test.ts`

```typescript
import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Hello VSCode Extension', () => {
    test('Extension activates', async () => {
        const ext = vscode.extensions.getExtension('simple.hello-extension');
        assert.ok(ext, 'Extension should be installed');

        await ext!.activate();
        assert.ok(ext!.isActive, 'Extension should activate');
    });

    test('Shows hello message', async () => {
        await vscode.commands.executeCommand('simple.hello');
        // Message shown (hard to assert in tests, but command executes)
    });
});
```

---

## Conclusion

**Best Practice for Simple:**
- ✅ Use **Playwright** for Electron app testing (JavaScript)
- ✅ Use **@vscode/test-electron** for VSCode extension testing (TypeScript)
- ❌ Don't use Rust for GUI testing (no mature tooling)
- ✅ Write tests in JavaScript/TypeScript (native to both platforms)

**Next Steps:**
1. Set up Playwright for Electron tests
2. Set up @vscode/test-electron for VSCode tests
3. Create "hello" examples with tests
4. Document testing workflow
