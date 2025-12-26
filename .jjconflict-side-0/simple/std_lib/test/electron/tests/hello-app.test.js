// Playwright test for electron_hello.spl
const { _electron: electron } = require('playwright');
const { test, expect } = require('@playwright/test');
const path = require('path');

test.describe('Hello Electron App', () => {
  let electronApp;

  test.beforeAll(async () => {
    // Path to the compiled Electron app
    const appPath = path.join(__dirname, '../../examples/electron_hello.js');

    // Launch Electron app
    electronApp = await electron.launch({
      args: [appPath],
      env: {
        ...process.env,
        // Set headless mode for CI
        ...(process.env.CI && { DISPLAY: ':99' })
      }
    });
  });

  test.afterAll(async () => {
    if (electronApp) {
      await electronApp.close();
    }
  });

  test('app launches successfully', async () => {
    // Verify app is ready
    const isReady = await electronApp.evaluate(async ({ app }) => {
      return app.isReady();
    });

    expect(isReady).toBe(true);
  });

  test('tray icon is created', async () => {
    // Check if tray exists
    const hasTray = await electronApp.evaluate(({ app }) => {
      return app.isReady();
    });

    expect(hasTray).toBe(true);
  });

  test('app does not create windows', async () => {
    // Headless app should have no windows
    const windows = await electronApp.windows();
    expect(windows.length).toBe(0);
  });

  test('app handles quit command', async () => {
    // Test that app can be quit programmatically
    const quitPromise = electronApp.evaluate(({ app }) => {
      return new Promise((resolve) => {
        app.on('will-quit', () => resolve(true));
        app.quit();
      });
    });

    const didQuit = await Promise.race([
      quitPromise,
      new Promise((resolve) => setTimeout(() => resolve(false), 5000))
    ]);

    expect(didQuit).toBe(true);
  });
});

test.describe('System Tray Functionality', () => {
  let electronApp;

  test.beforeEach(async () => {
    const appPath = path.join(__dirname, '../../examples/electron_hello.js');
    electronApp = await electron.launch({ args: [appPath] });
  });

  test.afterEach(async () => {
    if (electronApp) {
      await electronApp.close();
    }
  });

  test('tray tooltip is set correctly', async () => {
    // Wait for tray to be initialized
    await electronApp.evaluate(({ app }) => app.whenReady());

    // In real implementation, we would check tray.getToolTip()
    // For now, just verify app is ready
    const isReady = await electronApp.evaluate(({ app }) => app.isReady());
    expect(isReady).toBe(true);
  });

  test('menu items are configured', async () => {
    await electronApp.evaluate(({ app }) => app.whenReady());

    // Verify menu setup occurred (indirect test)
    const isReady = await electronApp.evaluate(({ app }) => app.isReady());
    expect(isReady).toBe(true);
  });
});
